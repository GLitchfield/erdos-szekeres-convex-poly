import ESBlueprint.B.ExistsCupStartLayersOfOneChangeNoCapFour
import ESBlueprint.B.MonochromaticSetInsertMaxOfOneChange
import ESBlueprint.B.IsStrongPolygonSetUnionOfCupCapCommonExtremes
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace ErdosSzekeres

/-- A four-cap-free set after an m-2-point cup has a strict triangular deficit if their one-change union avoids five-caps, m-cups and strong m+1-sets. Triangular equality forces full top cup-start rows, whose free edges assemble a forbidden common-endpoint strong polygon.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem card_lt_choose_of_ordered_cup_prefix_no_capFive_no_cup_no_strong {n m : ℕ} {χ : TripleColoring n} {Z W : Finset (Fin n)} (hm : 4 ≤ m) (hsep : ∀ x ∈ Z, ∀ y ∈ W, x < y) (hZcard : Z.card = m - 2) (hZcup : IsCupSet χ Z) (hone : OneChangeOn χ (Z ∪ W)) (hWnoCap : ¬ContainsCapSet χ W 4) (hnoCap : ¬ContainsCapSet χ (Z ∪ W) 5) (hnoCup : ¬ContainsCupSet χ (Z ∪ W) m) (hnoStrong : ¬ContainsStrongPolygonSet χ (Z ∪ W) (m + 1)) : W.card < Nat.choose m 2 := by
  classical
  let S := Z ∪ W
  have hZsub : Z ⊆ S := Finset.subset_union_left
  have hWsub : W ⊆ S := Finset.subset_union_right
  have hWone : OneChangeOn χ W := hone.mono hWsub
  have hsmall : ∀ (A : Finset (Fin n)), A ⊆ S → IsCupSet χ A → A.card < m := by
    intro A hAs hAcup
    by_contra h
    obtain ⟨D, hDA, hDcard⟩ := Finset.exists_subset_card_eq (show m ≤ A.card by omega)
    exact hnoCup ⟨D, hDA.trans hAs, hDcard, FinsetPolygon.IsCupSet.mono hAcup hDA⟩
  have hfour {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
      (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
      (hfirst : χ ⟨a, b, c, hab, hbc⟩ = Turn.right)
      (hlast : χ ⟨b, c, d, hbc, hcd⟩ = Turn.right) :
      IsCapSet χ {a, b, c, d} := by
    let f : Fin 4 ↪o Fin n := OrderEmbedding.ofStrictMono ![a, b, c, d] (by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      fin_cases i
      · simpa using hab
      · simpa using hbc
      · simpa using hcd)
    have hsub : Finset.univ.image f ⊆ S := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · simpa [f] using ha
      · simpa [f] using hb
      · simpa [f] using hc
      · simpa [f] using hd
    have hcap := FinsetPolygon.IsCap.image (isMonochromaticChain_finFour_of_outer_eq f
      (hone.mono hsub) (by simpa [f] using hfirst) (by simpa [f] using hlast))
    apply FinsetPolygon.IsCapSet.mono hcap
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp [f]⟩
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp [f]⟩
    · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, by simp [f]⟩
    · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, by simp [f]⟩
  have hfourCard {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d) :
      ({a, b, c, d} : Finset (Fin n)).card = 4 := by
    simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt hcd, ne_of_lt (hab.trans hbc),
      ne_of_lt (hbc.trans hcd), ne_of_lt (hab.trans (hbc.trans hcd))]
  have hfive {a b c d e : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
      (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) (he : e ∈ S)
      (h₁ : χ ⟨a, b, c, hab, hbc⟩ = Turn.right)
      (h₂ : χ ⟨b, c, d, hbc, hcd⟩ = Turn.right)
      (h₃ : χ ⟨c, d, e, hcd, hde⟩ = Turn.right) : False := by
    apply hnoCap
    let f : Fin 5 ↪o Fin n := OrderEmbedding.ofStrictMono ![a, b, c, d, e] (by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      fin_cases i
      · simpa using hab
      · simpa using hbc
      · simpa using hcd
      · simpa using hde)
    have hsub : Finset.univ.image f ⊆ S := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · simpa [f] using ha
      · simpa [f] using hb
      · simpa [f] using hc
      · simpa [f] using hd
      · simpa [f] using he
    refine ⟨Finset.univ.image f, hsub, ?_, ?_⟩
    · simpa using Finset.card_image_of_injective Finset.univ f.injective
    · exact FinsetPolygon.IsCap.image (isMonochromaticChain_finFive_of_consecutive f
        (hone.mono hsub) (by simpa [f] using h₁) (by simpa [f] using h₂)
        (by simpa [f] using h₃))
  obtain ⟨β, hatt, hmax, hrows⟩ := exists_cupStartLayers_of_oneChange_no_capFour hWone hWnoCap
  let row (j : ℕ) := W.filter (fun x ↦ β x = j)
  have hrange : ∀ x ∈ W, β x ∈ Finset.range m := by
    intro x hx
    obtain ⟨A, hAsub, _, hAcup, _, hAcard⟩ := hatt x hx
    apply Finset.mem_range.mpr
    rw [← hAcard]
    exact hsmall A (hAsub.trans hWsub) hAcup
  have hsumTri : ∀ v : ℕ, (∑ j ∈ Finset.range v, j) = Nat.choose v 2 := by
    intro v
    induction v with
    | zero => simp
    | succ v ih =>
      rw [Finset.sum_range_succ, ih]
      have hp : Nat.choose (v + 1) 2 = v + Nat.choose v 2 := by
        simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' v 1
      omega
  by_contra hlarge
  have hWlarge : Nat.choose m 2 ≤ W.card := by omega
  have hWsum : W.card = ∑ j ∈ Finset.range m, (row j).card :=
    Finset.card_eq_sum_card_fiberwise hrange
  have hsumBound : (∑ j ∈ Finset.range m, (row j).card) ≤ ∑ j ∈ Finset.range m, j :=
    Finset.sum_le_sum (fun j _ ↦ (hrows j).2)
  have hsumEq : (∑ j ∈ Finset.range m, (row j).card) = ∑ j ∈ Finset.range m, j := by
    apply le_antisymm hsumBound
    rw [hsumTri, ← hWsum]
    exact hWlarge
  have hfull : ∀ j < m, (row j).card = j := by
    intro j hj
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ ↦ (hrows i).2)).mp hsumEq
      j (Finset.mem_range.mpr hj)
  let F := row (m - 1)
  let G := row (m - 2)
  have hFcard : F.card = m - 1 := hfull _ (by omega)
  have hGcard : G.card = m - 2 := hfull _ (by omega)
  have hFcup : IsCupSet χ F := (hrows (m - 1)).1
  have hGcup : IsCupSet χ G := (hrows (m - 2)).1
  have hFsub : F ⊆ W := Finset.filter_subset _ _
  have hGsub : G ⊆ W := Finset.filter_subset _ _
  have hFβ : ∀ x ∈ F, β x = m - 1 := fun _ hx ↦ (Finset.mem_filter.mp hx).2
  have hGβ : ∀ x ∈ G, β x = m - 2 := fun _ hx ↦ (Finset.mem_filter.mp hx).2
  have hstartCap {x y : Fin n} (hx : x ∈ W) (hy : y ∈ W) (hxy : x < y)
      (hβeq : β x = β y) {A : Finset (Fin n)} (hAsub : A ⊆ W) (hyA : y ∈ A)
      (hAcup : IsCupSet χ A) (hAmin : ∀ t ∈ A, y ≤ t) (hAcard : A.card = β y)
      {e : Fin n} (heA : e ∈ A) (hye : y < e) (hAnext : ∀ t ∈ A, y < t → e ≤ t) :
      χ ⟨x, y, e, hxy, hye⟩ = Turn.right := by
    cases hcol : χ ⟨x, y, e, hxy, hye⟩ with
    | right => rfl
    | left =>
      exfalso
      have hnewSub : insert x A ⊆ W := Finset.insert_subset_iff.mpr ⟨hx, hAsub⟩
      have hnewCup : IsCupSet χ (insert x A) :=
        monochromaticSet_insert_min_of_oneChange hyA heA hye hxy hAmin hAnext
          hAcup (hWone.mono hnewSub) hcol
      have hnewMin : ∀ t ∈ insert x A, x ≤ t := by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact le_rfl
        · exact hxy.le.trans (hAmin t ht)
      have hbound := hmax x hx (insert x A) hnewSub (by simp) hnewCup hnewMin
      have hxNotA : x ∉ A := by
        intro hxA
        have := hAmin x hxA
        omega
      rw [Finset.card_insert_of_notMem hxNotA, hAcard] at hbound
      omega
  have hfree {x y : Fin n} (hx : x ∈ W) (hy : y ∈ W) (hxy : x < y)
      (hβeq : β x = β y) (hβTwo : 2 ≤ β y) :
      ∀ w ∈ W, (hwx : w < x) → χ ⟨w, x, y, hwx, hxy⟩ = Turn.left := by
    intro w hw hwx
    obtain ⟨A, hAsub, hyA, hAcup, hAmin, hAcard⟩ := hatt y hy
    have hrest : (A.erase y).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hyA, hAcard]
      omega
    let e := (A.erase y).min' hrest
    have heErase : e ∈ A.erase y := Finset.min'_mem _ _
    have heA : e ∈ A := (Finset.mem_erase.mp heErase).2
    have hye : y < e := by
      have := hAmin e heA
      have := (Finset.mem_erase.mp heErase).1
      omega
    have hAnext : ∀ t ∈ A, y < t → e ≤ t := by
      intro t ht hyt
      exact Finset.min'_le _ t (Finset.mem_erase.mpr ⟨ne_of_gt hyt, ht⟩)
    have hlast := hstartCap hx hy hxy hβeq hAsub hyA hAcup hAmin hAcard heA hye hAnext
    cases hfirst : χ ⟨w, x, y, hwx, hxy⟩ with
    | left => rfl
    | right =>
      exfalso
      apply hWnoCap
      refine ⟨{w, x, y, e}, ?_, hfourCard hwx hxy hye,
        hfour hwx hxy hye (hWsub hw) (hWsub hx) (hWsub hy) (hWsub (hAsub heA))
          hfirst hlast⟩
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hw, hx, hy, hAsub heA⟩
  have hfirstTwo (A : Finset (Fin n)) (hcard : 2 ≤ A.card) :
      ∃ a b, a ∈ A ∧ b ∈ A ∧ a < b ∧ (∀ x ∈ A, a ≤ x) ∧
        (∀ x ∈ A, a < x → b ≤ x) := by
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    let a := A.min' hne
    have ha : a ∈ A := Finset.min'_mem _ _
    have hrest : (A.erase a).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem ha]
      omega
    let b := (A.erase a).min' hrest
    have hb : b ∈ A.erase a := Finset.min'_mem _ _
    refine ⟨a, b, ha, (Finset.mem_erase.mp hb).2, ?_, ?_, ?_⟩
    · have := Finset.min'_le A b (Finset.mem_erase.mp hb).2
      have := (Finset.mem_erase.mp hb).1
      omega
    · exact fun x hx ↦ Finset.min'_le A x hx
    · intro x hx hax
      exact Finset.min'_le _ x (Finset.mem_erase.mpr ⟨ne_of_gt hax, hx⟩)
  have hlastTwo (A : Finset (Fin n)) (hcard : 2 ≤ A.card) :
      ∃ a b, a ∈ A ∧ b ∈ A ∧ a < b ∧ (∀ x ∈ A, x ≤ b) ∧
        (∀ x ∈ A, x < b → x ≤ a) := by
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    let b := A.max' hne
    have hb : b ∈ A := Finset.max'_mem _ _
    have hrest : (A.erase b).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hb]
      omega
    let a := (A.erase b).max' hrest
    have ha : a ∈ A.erase b := Finset.max'_mem _ _
    refine ⟨a, b, (Finset.mem_erase.mp ha).2, hb, ?_, ?_, ?_⟩
    · have := Finset.le_max' A a (Finset.mem_erase.mp ha).2
      have := (Finset.mem_erase.mp ha).1
      omega
    · exact fun x hx ↦ Finset.le_max' A x hx
    · intro x hx hxb
      exact Finset.le_max' _ x (Finset.mem_erase.mpr ⟨ne_of_lt hxb, hx⟩)
  have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
  let f1 := F.min' hFne
  have hf1F : f1 ∈ F := Finset.min'_mem _ _
  have hf1min : ∀ x ∈ F, f1 ≤ x := fun x hx ↦ Finset.min'_le _ x hx
  let Ft := F.erase f1
  have hFtcard : Ft.card = m - 2 := by
    dsimp [Ft]
    rw [Finset.card_erase_of_mem hf1F, hFcard]
    omega
  obtain ⟨f2, f3, hf2Ft, hf3Ft, hf23, hf2min, hf3next⟩ := hfirstTwo Ft (by omega)
  have hf2F : f2 ∈ F := (Finset.mem_erase.mp hf2Ft).2
  have hf3F : f3 ∈ F := (Finset.mem_erase.mp hf3Ft).2
  have hf12 : f1 < f2 := by
    have := hf1min f2 hf2F
    have := (Finset.mem_erase.mp hf2Ft).1
    omega
  have hf2next : ∀ x ∈ F, f1 < x → f2 ≤ x := by
    intro x hx hfx
    exact hf2min x (Finset.mem_erase.mpr ⟨ne_of_gt hfx, hx⟩)
  obtain ⟨fa, fl, hfaF, hflF, hfal, hflmax, hfaprev⟩ := hlastTwo F (by omega)
  obtain ⟨g1, g2, hg1G, hg2G, hg12, hg1min, hg2next⟩ := hfirstTwo G (by omega)
  obtain ⟨ga, gl, hgaG, hglG, hgal, hglmax, hgaprev⟩ := hlastTwo G (by omega)
  have hZne : Z.Nonempty := Finset.card_pos.mp (by omega)
  let p1 := Z.min' hZne
  have hp1Z : p1 ∈ Z := Finset.min'_mem _ _
  have hp1min : ∀ x ∈ Z, p1 ≤ x := fun x hx ↦ Finset.min'_le _ x hx
  obtain ⟨pa, z, hpaZ, hzZ, hpaz, hzmax, hpaprev⟩ := hlastTwo Z (by omega)
  have hFGne : ∀ x ∈ F, ∀ y ∈ G, x ≠ y := by
    intro x hx y hy hxy
    have := hFβ x hx
    have := hGβ y hy
    subst y
    omega
  have hattTwo {y : Fin n} (hy : y ∈ W) (hβ : 2 ≤ β y) :
      ∃ A e, A ⊆ W ∧ y ∈ A ∧ IsCupSet χ A ∧ (∀ t ∈ A, y ≤ t) ∧
        A.card = β y ∧ e ∈ A ∧ y < e ∧ (∀ t ∈ A, y < t → e ≤ t) := by
    obtain ⟨A, hAsub, hyA, hAcup, hAmin, hAcard⟩ := hatt y hy
    have hrest : (A.erase y).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hyA, hAcard]
      omega
    let e := (A.erase y).min' hrest
    have heErase : e ∈ A.erase y := Finset.min'_mem _ _
    have heA : e ∈ A := (Finset.mem_erase.mp heErase).2
    refine ⟨A, e, hAsub, hyA, hAcup, hAmin, hAcard, heA, ?_, ?_⟩
    · have := hAmin e heA
      have := (Finset.mem_erase.mp heErase).1
      omega
    · intro t ht hyt
      exact Finset.min'_le _ t (Finset.mem_erase.mpr ⟨ne_of_gt hyt, ht⟩)
  have hf2g1 : f2 < g1 := by
    by_contra h
    have hgf : g1 < f2 := by
      have := hFGne f2 hf2F g1 hg1G
      omega
    have hFtSub : Ft ⊆ W := (Finset.erase_subset _ _).trans hFsub
    have hnewSub : insert g1 Ft ⊆ W :=
      Finset.insert_subset_iff.mpr ⟨hGsub hg1G, hFtSub⟩
    have hfreeTurn := hfree (hFsub hf2F) (hFsub hf3F) hf23
      (by rw [hFβ _ hf2F, hFβ _ hf3F]) (by rw [hFβ _ hf3F]; omega)
      g1 (hGsub hg1G) hgf
    have hnewCup : IsCupSet χ (insert g1 Ft) :=
      monochromaticSet_insert_min_of_oneChange hf2Ft hf3Ft hf23 hgf hf2min hf3next
        (FinsetPolygon.IsCupSet.mono hFcup (Finset.erase_subset _ _))
        (hWone.mono hnewSub) hfreeTurn
    have hnewMin : ∀ t ∈ insert g1 Ft, g1 ≤ t := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact le_rfl
      · exact hgf.le.trans (hf2min t ht)
    have hbound := hmax g1 (hGsub hg1G) (insert g1 Ft) hnewSub (by simp) hnewCup hnewMin
    have hgNot : g1 ∉ Ft := by
      intro ht
      have := hf2min g1 ht
      omega
    rw [Finset.card_insert_of_notMem hgNot, hFtcard, hGβ _ hg1G] at hbound
    omega
  have hxf12 : ∀ x (hx : x ∈ Z),
      χ ⟨x, f1, f2, hsep x hx f1 (hFsub hf1F), hf12⟩ = Turn.right := by
    intro x hx
    have hxf : x < f1 := hsep x hx f1 (hFsub hf1F)
    cases hcol : χ ⟨x, f1, f2, hxf, hf12⟩ with
    | right => rfl
    | left =>
      exfalso
      have hsub : insert x F ⊆ S := Finset.insert_subset_iff.mpr ⟨hZsub hx, hFsub.trans hWsub⟩
      have hcup := monochromaticSet_insert_min_of_oneChange hf1F hf2F hf12 hxf
        hf1min hf2next hFcup (hone.mono hsub) hcol
      have hxNot : x ∉ F := by
        intro hxF
        have := hsep x hx x (hFsub hxF)
        omega
      have := hsmall _ hsub hcup
      rw [Finset.card_insert_of_notMem hxNot, hFcard] at this
      omega
  have hf12g1 : χ ⟨f1, f2, g1, hf12, hf2g1⟩ = Turn.right := by
    have hf2Gsub : insert f2 G ⊆ S :=
      Finset.insert_subset_iff.mpr ⟨hWsub (hFsub hf2F), hGsub.trans hWsub⟩
    have hfreeTurn := hfree (hGsub hg1G) (hGsub hg2G) hg12
      (by rw [hGβ _ hg1G, hGβ _ hg2G]) (by rw [hGβ _ hg2G]; omega)
      f2 (hFsub hf2F) hf2g1
    have hf2Gcup : IsCupSet χ (insert f2 G) :=
      monochromaticSet_insert_min_of_oneChange hg1G hg2G hg12 hf2g1 hg1min hg2next
        hGcup (hone.mono hf2Gsub) hfreeTurn
    cases hcol : χ ⟨f1, f2, g1, hf12, hf2g1⟩ with
    | right => rfl
    | left =>
      exfalso
      have hsub : insert f1 (insert f2 G) ⊆ S :=
        Finset.insert_subset_iff.mpr ⟨hWsub (hFsub hf1F), hf2Gsub⟩
      have hmin : ∀ x ∈ insert f2 G, f2 ≤ x := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact le_rfl
        · exact hf2g1.le.trans (hg1min x hx)
      have hnext : ∀ x ∈ insert f2 G, f2 < x → g1 ≤ x := by
        intro x hx hfx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · omega
        · exact hg1min x hx
      have hcup := monochromaticSet_insert_min_of_oneChange (by simp : f2 ∈ insert f2 G)
        (Finset.mem_insert_of_mem hg1G) hf2g1 hf12 hmin hnext hf2Gcup (hone.mono hsub) hcol
      have hf2Not : f2 ∉ G := fun hx ↦ hFGne f2 hf2F f2 hx rfl
      have hf1Not : f1 ∉ insert f2 G := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨ne_of_lt hf12, fun hx ↦ hFGne f1 hf1F f1 hx rfl⟩
      have := hsmall _ hsub hcup
      rw [Finset.card_insert_of_notMem hf1Not, Finset.card_insert_of_notMem hf2Not,
        hGcard] at this
      omega
  have hflgl : fl < gl := by
    by_contra h
    have hglfl : gl < fl := by
      have := hFGne fl hflF gl hglG
      omega
    obtain ⟨A, e, hAsub, hflA, hAcup, hAmin, hAcard, heA, hfle, hAnext⟩ :=
      hattTwo (hFsub hflF) (by rw [hFβ _ hflF]; omega)
    have hgle : χ ⟨gl, fl, e, hglfl, hfle⟩ = Turn.right := by
      cases hcol : χ ⟨gl, fl, e, hglfl, hfle⟩ with
      | right => rfl
      | left =>
        exfalso
        have hsub : insert gl A ⊆ S :=
          Finset.insert_subset_iff.mpr ⟨hWsub (hGsub hglG), hAsub.trans hWsub⟩
        have hcup := monochromaticSet_insert_min_of_oneChange hflA heA hfle hglfl
          hAmin hAnext hAcup (hone.mono hsub) hcol
        have hglNot : gl ∉ A := by
          intro hx
          have := hAmin gl hx
          omega
        have := hsmall _ hsub hcup
        rw [Finset.card_insert_of_notMem hglNot, hAcard, hFβ _ hflF] at this
        omega
    have hgalfl : χ ⟨ga, gl, fl, hgal, hglfl⟩ = Turn.left := by
      cases hcol : χ ⟨ga, gl, fl, hgal, hglfl⟩ with
      | left => rfl
      | right =>
        exfalso
        apply hWnoCap
        refine ⟨{ga, gl, fl, e}, ?_, hfourCard hgal hglfl hfle,
          hfour hgal hglfl hfle (hWsub (hGsub hgaG)) (hWsub (hGsub hglG))
            (hWsub (hFsub hflF)) (hWsub (hAsub heA)) hcol hgle⟩
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hGsub hgaG, hGsub hglG, hFsub hflF, hAsub heA⟩
    have hsub : insert fl G ⊆ W := Finset.insert_subset_iff.mpr ⟨hFsub hflF, hGsub⟩
    have hcup := monochromaticSet_insert_max_of_oneChange hgaG hglG hgal hglfl
      hglmax hgaprev hGcup (hWone.mono hsub) hgalfl
    have hmin : ∀ t ∈ insert fl G, g1 ≤ t := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact (hg1min gl hglG).trans hglfl.le
      · exact hg1min t ht
    have hbound := hmax g1 (hGsub hg1G) (insert fl G) hsub
      (Finset.mem_insert_of_mem hg1G) hcup hmin
    have hflNot : fl ∉ G := fun hx ↦ hFGne fl hflF fl hx rfl
    rw [Finset.card_insert_of_notMem hflNot, hGcard, hGβ _ hg1G] at hbound
    omega
  have hf1fl : f1 < fl := by
    have := hflmax f2 hf2F
    omega
  have hfalgl : χ ⟨fa, fl, gl, hfal, hflgl⟩ = Turn.right := by
    cases hcol : χ ⟨fa, fl, gl, hfal, hflgl⟩ with
    | right => rfl
    | left =>
      exfalso
      have hsub : insert gl F ⊆ S :=
        Finset.insert_subset_iff.mpr ⟨hWsub (hGsub hglG), hFsub.trans hWsub⟩
      have hcup := monochromaticSet_insert_max_of_oneChange hfaF hflF hfal hflgl
        hflmax hfaprev hFcup (hone.mono hsub) hcol
      have hglNot : gl ∉ F := fun hx ↦ hFGne gl hx gl hglG rfl
      have := hsmall _ hsub hcup
      rw [Finset.card_insert_of_notMem hglNot, hFcard] at this
      omega
  have hf1flgl : χ ⟨f1, fl, gl, hf1fl, hflgl⟩ = Turn.right := by
    obtain ⟨A, e, hAsub, hglA, hAcup, hAmin, hAcard, heA, hgle, hAnext⟩ :=
      hattTwo (hGsub hglG) (by rw [hGβ _ hglG]; omega)
    have hflgle : χ ⟨fl, gl, e, hflgl, hgle⟩ = Turn.left := by
      cases hcol : χ ⟨fl, gl, e, hflgl, hgle⟩ with
      | left => rfl
      | right =>
        exfalso
        apply hWnoCap
        refine ⟨{fa, fl, gl, e}, ?_, hfourCard hfal hflgl hgle,
          hfour hfal hflgl hgle (hWsub (hFsub hfaF)) (hWsub (hFsub hflF))
            (hWsub (hGsub hglG)) (hWsub (hAsub heA)) hfalgl hcol⟩
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hFsub hfaF, hFsub hflF, hGsub hglG, hAsub heA⟩
    have hflAsub : insert fl A ⊆ S :=
      Finset.insert_subset_iff.mpr ⟨hWsub (hFsub hflF), hAsub.trans hWsub⟩
    have hflAcup := monochromaticSet_insert_min_of_oneChange hglA heA hgle hflgl
      hAmin hAnext hAcup (hone.mono hflAsub) hflgle
    cases hcol : χ ⟨f1, fl, gl, hf1fl, hflgl⟩ with
    | right => rfl
    | left =>
      exfalso
      have hsub : insert f1 (insert fl A) ⊆ S :=
        Finset.insert_subset_iff.mpr ⟨hWsub (hFsub hf1F), hflAsub⟩
      have hmin : ∀ x ∈ insert fl A, fl ≤ x := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact le_rfl
        · exact hflgl.le.trans (hAmin x hx)
      have hnext : ∀ x ∈ insert fl A, fl < x → gl ≤ x := by
        intro x hx hfx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · omega
        · exact hAmin x hx
      have hcup := monochromaticSet_insert_min_of_oneChange (by simp : fl ∈ insert fl A)
        (Finset.mem_insert_of_mem hglA) hflgl hf1fl hmin hnext hflAcup (hone.mono hsub) hcol
      have hflNot : fl ∉ A := by
        intro hx
        have := hAmin fl hx
        omega
      have hf1Not : f1 ∉ insert fl A := by
        intro hx
        have := hmin f1 hx
        omega
      have := hsmall _ hsub hcup
      rw [Finset.card_insert_of_notMem hf1Not, Finset.card_insert_of_notMem hflNot,
        hAcard, hGβ _ hglG] at this
      omega
  have hbridge {C D : Finset (Fin n)} {l r : Fin n}
      (hCsub : C ⊆ S) (hDsub : D ⊆ S) (hlr : l < r)
      (hlC : l ∈ C) (hrC : r ∈ C) (hlD : l ∈ D) (hrD : r ∈ D)
      (hspan : ∀ x ∈ C ∪ D, l ≤ x ∧ x ≤ r)
      (hCcup : IsCupSet χ C) (hDcap : IsCapSet χ D)
      (hCcard : C.card = m - 1) (hDcard : D.card = 4) : False := by
    have hsub : C ∪ D ⊆ S := Finset.union_subset hCsub hDsub
    obtain ⟨hstrong, hinter⟩ := isStrongPolygonSet_union_of_cup_cap_common_extremes
      hlr hlC hrC hlD hrD hspan hCcup hDcap (hone.mono hsub)
    apply hnoStrong
    refine ⟨C ∪ D, hsub, ?_, hstrong⟩
    have hc := Finset.card_union_add_card_inter C D
    have hi : (C ∩ D).card = 2 := by rw [hinter]; simp [ne_of_lt hlr]
    omega
  have hzg1 : z < g1 := hsep z hzZ g1 (hGsub hg1G)
  have hzf1 : z < f1 := hsep z hzZ f1 (hFsub hf1F)
  have hp1f1 : p1 < f1 := hsep p1 hp1Z f1 (hFsub hf1F)
  cases hturn : χ ⟨pa, z, g1, hpaz, hzg1⟩ with
  | left =>
    let C := insert g1 Z
    let D : Finset (Fin n) := {p1, f1, f2, g1}
    have hCsub : C ⊆ S := Finset.insert_subset_iff.mpr ⟨hWsub (hGsub hg1G), hZsub⟩
    have hDsub : D ⊆ S := by
      simp only [D, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hZsub hp1Z, hWsub (hFsub hf1F), hWsub (hFsub hf2F), hWsub (hGsub hg1G)⟩
    have hCcup : IsCupSet χ C := monochromaticSet_insert_max_of_oneChange hpaZ hzZ hpaz hzg1
      hzmax hpaprev hZcup (hone.mono hCsub) hturn
    have hDcap : IsCapSet χ D := hfour hp1f1 hf12 hf2g1 (hZsub hp1Z)
      (hWsub (hFsub hf1F)) (hWsub (hFsub hf2F)) (hWsub (hGsub hg1G))
      (hxf12 p1 hp1Z) hf12g1
    have hspan : ∀ x ∈ C ∪ D, p1 ≤ x ∧ x ≤ g1 := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨(hp1f1.trans (hf12.trans hf2g1)).le, le_rfl⟩
        · exact ⟨hp1min x hx, (hsep x hx g1 (hGsub hg1G)).le⟩
      · simp only [D, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact ⟨le_rfl, (hp1f1.trans (hf12.trans hf2g1)).le⟩
        · exact ⟨hp1f1.le, (hf12.trans hf2g1).le⟩
        · exact ⟨(hp1f1.trans hf12).le, hf2g1.le⟩
        · exact ⟨(hp1f1.trans (hf12.trans hf2g1)).le, le_rfl⟩
    have hg1NotZ : g1 ∉ Z := by
      intro hx
      have := hsep g1 hx g1 (hGsub hg1G)
      omega
    have hCcard : C.card = m - 1 := by
      dsimp [C]
      rw [Finset.card_insert_of_notMem hg1NotZ, hZcard]
      omega
    exact hbridge hCsub hDsub (hp1f1.trans (hf12.trans hf2g1))
      (Finset.mem_insert_of_mem hp1Z) (by simp [C]) (by simp [D]) (by simp [D])
      hspan hCcup hDcap hCcard (hfourCard hp1f1 hf12 hf2g1)
  | right =>
    have hzg12 : χ ⟨z, g1, g2, hzg1, hg12⟩ = Turn.left := by
      obtain ⟨A, e, hAsub, hg2A, hAcup, hAmin, hAcard, heA, hg2e, hAnext⟩ :=
        hattTwo (hGsub hg2G) (by rw [hGβ _ hg2G]; omega)
      have hg12e := hstartCap (hGsub hg1G) (hGsub hg2G) hg12
        (by rw [hGβ _ hg1G, hGβ _ hg2G]) hAsub hg2A hAcup hAmin hAcard heA hg2e hAnext
      cases hcol : χ ⟨z, g1, g2, hzg1, hg12⟩ with
      | left => rfl
      | right =>
        exact (hfive hpaz hzg1 hg12 hg2e (hZsub hpaZ) (hZsub hzZ)
          (hWsub (hGsub hg1G)) (hWsub (hGsub hg2G)) (hWsub (hAsub heA))
          hturn hcol hg12e).elim
    have hpazf1 : χ ⟨pa, z, f1, hpaz, hzf1⟩ = Turn.left := by
      obtain ⟨A, e, hAsub, hf2A, hAcup, hAmin, hAcard, heA, hf2e, hAnext⟩ :=
        hattTwo (hFsub hf2F) (by rw [hFβ _ hf2F]; omega)
      have hf12e := hstartCap (hFsub hf1F) (hFsub hf2F) hf12
        (by rw [hFβ _ hf1F, hFβ _ hf2F]) hAsub hf2A hAcup hAmin hAcard heA hf2e hAnext
      cases hcol : χ ⟨pa, z, f1, hpaz, hzf1⟩ with
      | left => rfl
      | right =>
        exact (hfive hpaz hzf1 hf12 hf2e (hZsub hpaZ) (hZsub hzZ)
          (hWsub (hFsub hf1F)) (hWsub (hFsub hf2F)) (hWsub (hAsub heA))
          hcol (hxf12 z hzZ) hf12e).elim
    have hf1Zsub : insert f1 Z ⊆ S :=
      Finset.insert_subset_iff.mpr ⟨hWsub (hFsub hf1F), hZsub⟩
    have hf1Zcup := monochromaticSet_insert_max_of_oneChange hpaZ hzZ hpaz hzf1
      hzmax hpaprev hZcup (hone.mono hf1Zsub) hpazf1
    have hzf1fl : χ ⟨z, f1, fl, hzf1, hf1fl⟩ = Turn.right := by
      cases hcol : χ ⟨z, f1, fl, hzf1, hf1fl⟩ with
      | right => rfl
      | left =>
        exfalso
        have hsub : insert fl (insert f1 Z) ⊆ S :=
          Finset.insert_subset_iff.mpr ⟨hWsub (hFsub hflF), hf1Zsub⟩
        have hmax : ∀ x ∈ insert f1 Z, x ≤ f1 := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact le_rfl
          · exact (hsep x hx f1 (hFsub hf1F)).le
        have hprev : ∀ x ∈ insert f1 Z, x < f1 → x ≤ z := by
          intro x hx hxf
          rcases Finset.mem_insert.mp hx with rfl | hx
          · omega
          · exact hzmax x hx
        have hcup := monochromaticSet_insert_max_of_oneChange (Finset.mem_insert_of_mem hzZ)
          (by simp : f1 ∈ insert f1 Z) hzf1 hf1fl hmax hprev hf1Zcup (hone.mono hsub) hcol
        have hf1NotZ : f1 ∉ Z := by
          intro hx
          have := hsep f1 hx f1 (hFsub hf1F)
          omega
        have hflNot : fl ∉ insert f1 Z := by
          intro hx
          have := hmax fl hx
          omega
        have := hsmall _ hsub hcup
        rw [Finset.card_insert_of_notMem hflNot, Finset.card_insert_of_notMem hf1NotZ,
          hZcard] at this
        omega
    let C := insert z G
    let D : Finset (Fin n) := {z, f1, fl, gl}
    have hCsub : C ⊆ S := Finset.insert_subset_iff.mpr ⟨hZsub hzZ, hGsub.trans hWsub⟩
    have hDsub : D ⊆ S := by
      simp only [D, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hZsub hzZ, hWsub (hFsub hf1F), hWsub (hFsub hflF), hWsub (hGsub hglG)⟩
    have hCcup : IsCupSet χ C := monochromaticSet_insert_min_of_oneChange hg1G hg2G hg12 hzg1
      hg1min hg2next hGcup (hone.mono hCsub) hzg12
    have hDcap : IsCapSet χ D := hfour hzf1 hf1fl hflgl (hZsub hzZ)
      (hWsub (hFsub hf1F)) (hWsub (hFsub hflF)) (hWsub (hGsub hglG)) hzf1fl hf1flgl
    have hspan : ∀ x ∈ C ∪ D, z ≤ x ∧ x ≤ gl := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨le_rfl, hzg1.le.trans (hg1min gl hglG)⟩
        · exact ⟨(hsep z hzZ x (hGsub hx)).le, hglmax x hx⟩
      · simp only [D, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact ⟨le_rfl, (hzf1.trans (hf1fl.trans hflgl)).le⟩
        · exact ⟨hzf1.le, (hf1fl.trans hflgl).le⟩
        · exact ⟨(hzf1.trans hf1fl).le, hflgl.le⟩
        · exact ⟨(hzf1.trans (hf1fl.trans hflgl)).le, le_rfl⟩
    have hzNotG : z ∉ G := by
      intro hx
      have := hsep z hzZ z (hGsub hx)
      omega
    have hCcard : C.card = m - 1 := by
      dsimp [C]
      rw [Finset.card_insert_of_notMem hzNotG, hGcard]
      omega
    exact hbridge hCsub hDsub (hzf1.trans (hf1fl.trans hflgl))
      (by simp [C]) (Finset.mem_insert_of_mem hglG) (by simp [D]) (by simp [D])
      hspan hCcup hDcap hCcard (hfourCard hzf1 hf1fl hflgl)

end ErdosSzekeres
