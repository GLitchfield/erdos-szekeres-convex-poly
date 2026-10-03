import ESBlueprint.B.MonochromaticSetInsertMaxOfOneChange
import ESBlueprint.B.MonochromaticSetInsertMinOfOneChange

namespace ErdosSzekeres

/-- If every m-cup straddles a marker and the ambient set has no m+1-cup and four-cap-free sides at a possibly different missing gap, at least one family of first or last m-cup endpoints has no three-cap. Opposing cap triples force incompatible four-point turn sequences across the two gaps.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem markerCupEndpoints_no_capThree_on_one_side {n m : ℕ} {χ : TripleColoring n} {s E F : Finset (Fin n)} {q h : Fin n} (hm : 3 ≤ m) (hq : q ∉ s) (hone : OneChangeOn χ s) (hleft : ¬ContainsCapSet χ (s.filter (fun x ↦ x < q)) 4) (hright : ¬ContainsCapSet χ (s.filter (fun x ↦ q < x)) 4) (hnoCup : ¬ContainsCupSet χ s (m + 1)) (hstraddle : ∀ C : Finset (Fin n), C ⊆ s → C.card = m → IsCupSet χ C → (∃ x ∈ C, x < h) ∧ ∃ y ∈ C, h < y) (hE : ∀ e ∈ E, ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = m ∧ IsCupSet χ C ∧ e ∈ C ∧ ∀ x ∈ C, e ≤ x) (hF : ∀ f ∈ F, ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = m ∧ IsCupSet χ C ∧ f ∈ C ∧ ∀ x ∈ C, x ≤ f) : ¬ContainsCapSet χ E 3 ∨ ¬ContainsCapSet χ F 3 := by
  classical
  have hEs : E ⊆ s := by
    intro x hx
    obtain ⟨C, hCs, _, _, hxC, _⟩ := hE x hx
    exact hCs hxC
  have hFs : F ⊆ s := by
    intro x hx
    obtain ⟨C, hCs, _, _, hxC, _⟩ := hF x hx
    exact hCs hxC
  by_contra hboth
  push Not at hboth
  obtain ⟨CE, hCEE, hCEcard, hCEcap⟩ := hboth.1
  obtain ⟨CF, hCFF, hCFcard, hCFcap⟩ := hboth.2
  let u : Fin 3 ↪o Fin n := CE.orderEmbOfFin hCEcard
  let v : Fin 3 ↪o Fin n := CF.orderEmbOfFin hCFcard
  let a := u 0
  let b := u 1
  let e := u 2
  let f := v 0
  let c := v 1
  let d := v 2
  have hab : a < b := u.strictMono (by decide)
  have hbe : b < e := u.strictMono (by decide)
  have hfc : f < c := v.strictMono (by decide)
  have hcd : c < d := v.strictMono (by decide)
  have haCE : a ∈ CE := CE.orderEmbOfFin_mem hCEcard 0
  have hbCE : b ∈ CE := CE.orderEmbOfFin_mem hCEcard 1
  have heCE : e ∈ CE := CE.orderEmbOfFin_mem hCEcard 2
  have hfCF : f ∈ CF := CF.orderEmbOfFin_mem hCFcard 0
  have hcCF : c ∈ CF := CF.orderEmbOfFin_mem hCFcard 1
  have hdCF : d ∈ CF := CF.orderEmbOfFin_mem hCFcard 2
  have haS := hEs (hCEE haCE)
  have hbS := hEs (hCEE hbCE)
  have heS := hEs (hCEE heCE)
  have hfS := hFs (hCFF hfCF)
  have hcS := hFs (hCFF hcCF)
  have hdS := hFs (hCFF hdCF)
  have habe : χ ⟨a, b, e, hab, hbe⟩ = Turn.right := hCEcap _ haCE hbCE heCE
  have hfcd : χ ⟨f, c, d, hfc, hcd⟩ = Turn.right := hCFcap _ hfCF hcCF hdCF
  obtain ⟨D, hDs, hDcard, hDcup, heD, hemin⟩ := hE e (hCEE heCE)
  obtain ⟨C, hCs, hCcard, hCcup, hfC, hfmax⟩ := hF f (hCFF hfCF)
  have hfour {w x y z : Fin n} (hwx : w < x) (hxy : x < y) (hyz : y < z)
      (hw : w ∈ s) (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s)
      (hfirst : χ ⟨w, x, y, hwx, hxy⟩ = Turn.right)
      (hlast : χ ⟨x, y, z, hxy, hyz⟩ = Turn.right) :
      IsCapSet χ {w, x, y, z} := by
    let g : Fin 4 ↪o Fin n := OrderEmbedding.ofStrictMono ![w, x, y, z] (by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      fin_cases i
      · simpa using hwx
      · simpa using hxy
      · simpa using hyz)
    have hsub : Finset.univ.image g ⊆ s := by
      intro t ht
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht
      obtain ⟨i, rfl⟩ := ht
      fin_cases i
      · simpa [g] using hw
      · simpa [g] using hx
      · simpa [g] using hy
      · simpa [g] using hz
    have hcap := FinsetPolygon.IsCap.image (isMonochromaticChain_finFour_of_outer_eq g
      (hone.mono hsub) (by simpa [g] using hfirst) (by simpa [g] using hlast))
    apply FinsetPolygon.IsCapSet.mono hcap
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp [g]⟩
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp [g]⟩
    · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, by simp [g]⟩
    · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, by simp [g]⟩
  have hfourCard {w x y z : Fin n} (hwx : w < x) (hxy : x < y) (hyz : y < z) :
      ({w, x, y, z} : Finset (Fin n)).card = 4 := by
    simp [ne_of_lt hwx, ne_of_lt hxy, ne_of_lt hyz, ne_of_lt (hwx.trans hxy),
      ne_of_lt (hxy.trans hyz), ne_of_lt (hwx.trans (hxy.trans hyz))]
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
  obtain ⟨d2, d3, hd2Dt, hd3Dt, hd23, hd2min, hd3next⟩ := hfirstTwo Dt (by omega)
  obtain ⟨c1, c2, hc1Ct, hc2Ct, hc12, hc2max, hc1prev⟩ := hlastTwo Ct (by omega)
  have hd2D := (Finset.mem_erase.mp hd2Dt).2
  have hd3D := (Finset.mem_erase.mp hd3Dt).2
  have hc1C := (Finset.mem_erase.mp hc1Ct).2
  have hc2C := (Finset.mem_erase.mp hc2Ct).2
  have hd2S := hDs hd2D
  have hd3S := hDs hd3D
  have hc1S := hCs hc1C
  have hc2S := hCs hc2C
  have hed2 : e < d2 := by
    have := hemin d2 hd2D
    have := (Finset.mem_erase.mp hd2Dt).1
    omega
  have hc2f : c2 < f := by
    have := hfmax c2 hc2C
    have := (Finset.mem_erase.mp hc2Ct).1
    omega
  have hd2next : ∀ x ∈ D, e < x → d2 ≤ x := by
    intro x hx hex
    exact hd2min x (Finset.mem_erase.mpr ⟨ne_of_gt hex, hx⟩)
  have hc2prev : ∀ x ∈ C, x < f → x ≤ c2 := by
    intro x hx hxf
    exact hc2max x (Finset.mem_erase.mpr ⟨ne_of_lt hxf, hx⟩)
  have heh : e < h := by
    obtain ⟨x, hx, hxh⟩ := (hstraddle D hDs hDcard hDcup).1
    exact (hemin x hx).trans_lt hxh
  have hhf : h < f := by
    obtain ⟨x, hx, hhx⟩ := (hstraddle C hCs hCcard hCcup).2
    exact hhx.trans_le (hfmax x hx)
  have hS1left : ∀ x ∈ s, (hxe : x < e) → χ ⟨x, e, d2, hxe, hed2⟩ = Turn.right := by
    intro x hx hxe
    cases hturn : χ ⟨x, e, d2, hxe, hed2⟩ with
    | right => rfl
    | left =>
      exfalso
      have hsub : insert x D ⊆ s := Finset.insert_subset_iff.mpr ⟨hx, hDs⟩
      have hcup := monochromaticSet_insert_min_of_oneChange heD hd2D hed2 hxe
        hemin hd2next hDcup (hone.mono hsub) hturn
      have hxNotD : x ∉ D := by
        intro hxD
        have := hemin x hxD
        omega
      exact hnoCup ⟨insert x D, hsub,
        by rw [Finset.card_insert_of_notMem hxNotD, hDcard], hcup⟩
  have hS1right : ∀ y ∈ s, (hfy : f < y) → χ ⟨c2, f, y, hc2f, hfy⟩ = Turn.right := by
    intro y hy hfy
    cases hturn : χ ⟨c2, f, y, hc2f, hfy⟩ with
    | right => rfl
    | left =>
      exfalso
      have hsub : insert y C ⊆ s := Finset.insert_subset_iff.mpr ⟨hy, hCs⟩
      have hcup := monochromaticSet_insert_max_of_oneChange hc2C hfC hc2f hfy
        hfmax hc2prev hCcup (hone.mono hsub) hturn
      have hyNotC : y ∉ C := by
        intro hyC
        have := hfmax y hyC
        omega
      exact hnoCup ⟨insert y C, hsub,
        by rw [Finset.card_insert_of_notMem hyNotC, hCcard], hcup⟩
  have hleftFour {w x y z : Fin n} (hwx : w < x) (hxy : x < y) (hyz : y < z)
      (hw : w ∈ s) (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (hzq : z < q)
      (hfirst : χ ⟨w, x, y, hwx, hxy⟩ = Turn.right)
      (hlast : χ ⟨x, y, z, hxy, hyz⟩ = Turn.right) : False := by
    apply hleft
    refine ⟨{w, x, y, z}, ?_, hfourCard hwx hxy hyz,
      hfour hwx hxy hyz hw hx hy hz hfirst hlast⟩
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨Finset.mem_filter.mpr ⟨hw, (hwx.trans (hxy.trans hyz)).trans hzq⟩,
      Finset.mem_filter.mpr ⟨hx, (hxy.trans hyz).trans hzq⟩,
      Finset.mem_filter.mpr ⟨hy, hyz.trans hzq⟩, Finset.mem_filter.mpr ⟨hz, hzq⟩⟩
  have hrightFour {w x y z : Fin n} (hwx : w < x) (hxy : x < y) (hyz : y < z)
      (hw : w ∈ s) (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (hqw : q < w)
      (hfirst : χ ⟨w, x, y, hwx, hxy⟩ = Turn.right)
      (hlast : χ ⟨x, y, z, hxy, hyz⟩ = Turn.right) : False := by
    apply hright
    refine ⟨{w, x, y, z}, ?_, hfourCard hwx hxy hyz,
      hfour hwx hxy hyz hw hx hy hz hfirst hlast⟩
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨Finset.mem_filter.mpr ⟨hw, hqw⟩, Finset.mem_filter.mpr ⟨hx, hqw.trans hwx⟩,
      Finset.mem_filter.mpr ⟨hy, hqw.trans (hwx.trans hxy)⟩,
      Finset.mem_filter.mpr ⟨hz, hqw.trans (hwx.trans (hxy.trans hyz))⟩⟩
  have hspanFour {w x y z : Fin n} (hwx : w < x) (hxy : x < y) (hyz : y < z)
      (hw : w ∈ s) (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s)
      (hfirst : χ ⟨w, x, y, hwx, hxy⟩ = Turn.right)
      (hlast : χ ⟨x, y, z, hxy, hyz⟩ = Turn.right) : w < q ∧ q < z := by
    constructor
    · by_contra h
      have hwq : w ≠ q := by rintro rfl; exact hq hw
      have hqw : q < w := by omega
      exact hrightFour hwx hxy hyz hw hx hy hz hqw hfirst hlast
    · by_contra h
      have hzq : z ≠ q := by rintro rfl; exact hq hz
      have hzlt : z < q := by omega
      exact hleftFour hwx hxy hyz hw hx hy hz hzlt hfirst hlast
  have hfirstSpan := hspanFour hab hbe hed2 haS hbS heS hd2S habe (hS1left b hbS hbe)
  have hlastSpan := hspanFour hc2f hfc hcd hc2S hfS hcS hdS (hS1right c hcS hfc) hfcd
  have hc2d2 : c2 < d2 := hlastSpan.1.trans hfirstSpan.2
  have hCtSub : Ct ⊆ s := (Finset.erase_subset _ _).trans hCs
  have hDtSub : Dt ⊆ s := (Finset.erase_subset _ _).trans hDs
  have hCtCup : IsCupSet χ Ct := FinsetPolygon.IsCupSet.mono hCcup (Finset.erase_subset _ _)
  have hDtCup : IsCupSet χ Dt := FinsetPolygon.IsCupSet.mono hDcup (Finset.erase_subset _ _)
  have hS4left : ∀ y ∈ s, (hc2y : c2 < y) → y < h →
      χ ⟨c1, c2, y, hc12, hc2y⟩ = Turn.right := by
    intro y hy hc2y hyh
    cases hturn : χ ⟨c1, c2, y, hc12, hc2y⟩ with
    | right => rfl
    | left =>
      exfalso
      have hsub : insert y Ct ⊆ s := Finset.insert_subset_iff.mpr ⟨hy, hCtSub⟩
      have hcup := monochromaticSet_insert_max_of_oneChange hc1Ct hc2Ct hc12 hc2y
        hc2max hc1prev hCtCup (hone.mono hsub) hturn
      have hyNot : y ∉ Ct := by
        intro ht
        have := hc2max y ht
        omega
      have hcard : (insert y Ct).card = m := by
        rw [Finset.card_insert_of_notMem hyNot, hCtcard]
        omega
      obtain ⟨x, hx, hhx⟩ := (hstraddle _ hsub hcard hcup).2
      have hxh : x < h := by
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hyh
        · exact (hc2max x hx).trans_lt (hc2y.trans hyh)
      omega
  have hS4right : ∀ x ∈ s, h < x → (hxd2 : x < d2) →
      χ ⟨x, d2, d3, hxd2, hd23⟩ = Turn.right := by
    intro x hx hhx hxd2
    cases hturn : χ ⟨x, d2, d3, hxd2, hd23⟩ with
    | right => rfl
    | left =>
      exfalso
      have hsub : insert x Dt ⊆ s := Finset.insert_subset_iff.mpr ⟨hx, hDtSub⟩
      have hcup := monochromaticSet_insert_min_of_oneChange hd2Dt hd3Dt hd23 hxd2
        hd2min hd3next hDtCup (hone.mono hsub) hturn
      have hxNot : x ∉ Dt := by
        intro ht
        have := hd2min x ht
        omega
      have hcard : (insert x Dt).card = m := by
        rw [Finset.card_insert_of_notMem hxNot, hDtcard]
        omega
      obtain ⟨y, hy, hyh⟩ := (hstraddle _ hsub hcard hcup).1
      have hhy : h < y := by
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hhx
        · exact (hhx.trans hxd2).trans_le (hd2min y hy)
      omega
  have hS4both (hfirst : χ ⟨c1, c2, d2, hc12, hc2d2⟩ = Turn.left)
      (hlast : χ ⟨c2, d2, d3, hc2d2, hd23⟩ = Turn.left) : False := by
    have hd2Sub : insert d2 Ct ⊆ s := Finset.insert_subset_iff.mpr ⟨hd2S, hCtSub⟩
    have hd2Cup := monochromaticSet_insert_max_of_oneChange hc1Ct hc2Ct hc12 hc2d2
      hc2max hc1prev hCtCup (hone.mono hd2Sub) hfirst
    have hsub : insert d3 (insert d2 Ct) ⊆ s :=
      Finset.insert_subset_iff.mpr ⟨hd3S, hd2Sub⟩
    have hmax : ∀ x ∈ insert d2 Ct, x ≤ d2 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact (hc2max x hx).trans hc2d2.le
    have hprev : ∀ x ∈ insert d2 Ct, x < d2 → x ≤ c2 := by
      intro x hx hxd
      rcases Finset.mem_insert.mp hx with rfl | hx
      · omega
      · exact hc2max x hx
    have hcup := monochromaticSet_insert_max_of_oneChange (Finset.mem_insert_of_mem hc2Ct)
      (by simp : d2 ∈ insert d2 Ct) hc2d2 hd23 hmax hprev hd2Cup (hone.mono hsub) hlast
    have hd2Not : d2 ∉ Ct := by
      intro hx
      have := hc2max d2 hx
      omega
    have hd3Not : d3 ∉ insert d2 Ct := by
      intro hx
      have := hmax d3 hx
      omega
    have hcard : (insert d3 (insert d2 Ct)).card = m + 1 := by
      rw [Finset.card_insert_of_notMem hd3Not, Finset.card_insert_of_notMem hd2Not, hCtcard]
      omega
    exact hnoCup ⟨_, hsub, hcard, hcup⟩
  have heDturn : χ ⟨e, d2, d3, hed2, hd23⟩ = Turn.left := hDcup _ heD hd2D hd3D
  have hfCturn : χ ⟨c1, c2, f, hc12, hc2f⟩ = Turn.left := hCcup _ hc1C hc2C hfC
  have hX (hec2 : e < c2)
      (hcap : χ ⟨c2, d2, d3, hc2d2, hd23⟩ = Turn.right) : False := by
    have hseq := hone hec2 hc2d2 hd23 heS hc2S hd2S hd3S
    have hne : χ ⟨e, d2, d3, hed2, hd23⟩ ≠ χ ⟨c2, d2, d3, hc2d2, hd23⟩ := by
      rw [heDturn, hcap]
      decide
    have hhead := hseq.head_eq_of_third_ne_fourth hne
    have hec2d2 : χ ⟨e, c2, d2, hec2, hc2d2⟩ = Turn.left :=
      hhead.1.trans (hhead.2.trans heDturn)
    have hseq2 := hone hbe hec2 hc2d2 hbS heS hc2S hd2S
    have hbcap := hS1left b hbS hbe
    have hne2 : χ ⟨b, e, d2, hbe, hed2⟩ ≠ χ ⟨e, c2, d2, hec2, hc2d2⟩ := by
      rw [hbcap, hec2d2]
      decide
    have hbec2 : χ ⟨b, e, c2, hbe, hec2⟩ = Turn.right :=
      (hseq2.first_eq_second_of_second_ne_fourth hne2).trans hbcap
    exact hleftFour hab hbe hec2 haS hbS heS hc2S hlastSpan.1 habe hbec2
  have hXprime (hd2f : d2 < f)
      (hcap : χ ⟨c1, c2, d2, hc12, hc2d2⟩ = Turn.right) : False := by
    have hseq := hone hc12 hc2d2 hd2f hc1S hc2S hd2S hfS
    have hne : χ ⟨c1, c2, d2, hc12, hc2d2⟩ ≠ χ ⟨c1, c2, f, hc12, hc2f⟩ := by
      rw [hcap, hfCturn]
      decide
    have htail := hseq.tail_eq_of_first_ne_second hne
    have hc2d2f : χ ⟨c2, d2, f, hc2d2, hd2f⟩ = Turn.left :=
      htail.2.symm.trans (htail.1.symm.trans hfCturn)
    have hseq2 := hone hc2d2 hd2f hfc hc2S hd2S hfS hcS
    have hccap := hS1right c hcS hfc
    have hne2 : χ ⟨c2, d2, f, hc2d2, hd2f⟩ ≠ χ ⟨c2, f, c, hc2f, hfc⟩ := by
      rw [hc2d2f, hccap]
      decide
    have hd2fc : χ ⟨d2, f, c, hd2f, hfc⟩ = Turn.right :=
      (hseq2.third_eq_fourth_of_first_ne_third hne2).symm.trans hccap
    exact hrightFour hd2f hfc hcd hd2S hfS hcS hdS hfirstSpan.2 hd2fc hfcd
  have hcaseLeft (hfirst : χ ⟨c1, c2, d2, hc12, hc2d2⟩ = Turn.left)
      (hlast : χ ⟨c2, d2, d3, hc2d2, hd23⟩ = Turn.right) : False := by
    have heNe : e ≠ c2 := by
      intro heq
      have hcup : χ ⟨c2, d2, d3, hc2d2, hd23⟩ = Turn.left := by
        simpa only [heq] using heDturn
      rw [hlast] at hcup
      cases hcup
    by_cases hec2 : e < c2
    · exact hX hec2 hlast
    have hc2e : c2 < e := by omega
    have hcap := hS1left c2 hc2S hc2e
    have hseq := hone hc12 hc2e hed2 hc1S hc2S heS hd2S
    have hne : χ ⟨c1, c2, d2, hc12, hc2d2⟩ ≠ χ ⟨c2, e, d2, hc2e, hed2⟩ := by
      rw [hfirst, hcap]
      decide
    have hc1c2e : χ ⟨c1, c2, e, hc12, hc2e⟩ = Turn.left :=
      (hseq.first_eq_second_of_second_ne_fourth hne).trans hfirst
    have hwrong := hS4left e heS hc2e heh
    rw [hc1c2e] at hwrong
    cases hwrong
  have hcaseRight (hfirst : χ ⟨c1, c2, d2, hc12, hc2d2⟩ = Turn.right)
      (hlast : χ ⟨c2, d2, d3, hc2d2, hd23⟩ = Turn.left) : False := by
    have hdNe : d2 ≠ f := by
      intro heq
      have hfd3 : f < d3 := by omega
      have hcup : χ ⟨c2, f, d3, hc2f, hfd3⟩ = Turn.left := by
        simpa only [heq] using hlast
      rw [hS1right d3 hd3S hfd3] at hcup
      cases hcup
    by_cases hd2f : d2 < f
    · exact hXprime hd2f hfirst
    have hfd2 : f < d2 := by omega
    have hcap := hS1right d2 hd2S hfd2
    have hseq := hone hc2f hfd2 hd23 hc2S hfS hd2S hd3S
    have hne : χ ⟨c2, f, d2, hc2f, hfd2⟩ ≠ χ ⟨c2, d2, d3, hc2d2, hd23⟩ := by
      rw [hcap, hlast]
      decide
    have hfd23 : χ ⟨f, d2, d3, hfd2, hd23⟩ = Turn.left :=
      (hseq.third_eq_fourth_of_first_ne_third hne).symm.trans hlast
    have hwrong := hS4right f hfS hhf hfd2
    rw [hfd23] at hwrong
    cases hwrong
  have hcaseCaps (hfirst : χ ⟨c1, c2, d2, hc12, hc2d2⟩ = Turn.right)
      (hlast : χ ⟨c2, d2, d3, hc2d2, hd23⟩ = Turn.right) : False := by
    have heNe : e ≠ c2 := by
      intro heq
      have hcup : χ ⟨c2, d2, d3, hc2d2, hd23⟩ = Turn.left := by
        simpa only [heq] using heDturn
      rw [hlast] at hcup
      cases hcup
    have hdNe : d2 ≠ f := by
      intro heq
      have hcap : χ ⟨c1, c2, f, hc12, hc2f⟩ = Turn.right := by
        simpa only [heq] using hfirst
      rw [hfCturn] at hcap
      cases hcap
    have hc2e : c2 < e := by
      by_contra h
      have hec2 : e < c2 := by omega
      exact hX hec2 hlast
    have hfd2 : f < d2 := by
      by_contra h
      have hd2f : d2 < f := by omega
      exact hXprime hd2f hfirst
    have hef : e < f := heh.trans hhf
    have hc1c2e := hS4left e heS hc2e heh
    have hseq := hone hc12 hc2e hef hc1S hc2S heS hfS
    have hne : χ ⟨c1, c2, e, hc12, hc2e⟩ ≠ χ ⟨c1, c2, f, hc12, hc2f⟩ := by
      rw [hc1c2e, hfCturn]
      decide
    have htail := hseq.tail_eq_of_first_ne_second hne
    have hc2ef : χ ⟨c2, e, f, hc2e, hef⟩ = Turn.left :=
      htail.2.symm.trans (htail.1.symm.trans hfCturn)
    have hc2fd2 := hS1right d2 hd2S hfd2
    have hfd23 := hS4right f hfS hhf hfd2
    have hseq2 := hone hef hfd2 hd23 heS hfS hd2S hd3S
    have hne2 : χ ⟨e, d2, d3, hed2, hd23⟩ ≠ χ ⟨f, d2, d3, hfd2, hd23⟩ := by
      rw [heDturn, hfd23]
      decide
    have hhead := hseq2.head_eq_of_third_ne_fourth hne2
    have hefd2 : χ ⟨e, f, d2, hef, hfd2⟩ = Turn.left :=
      hhead.1.trans (hhead.2.trans heDturn)
    have hseq3 := hone hc2e hef hfd2 hc2S heS hfS hd2S
    have hall := hseq3.all_eq_of_outer_eq (hc2ef.trans hefd2.symm)
    have hwrong := hall.2.2
    rw [hc2fd2, hefd2] at hwrong
    cases hwrong
  cases hfirst : χ ⟨c1, c2, d2, hc12, hc2d2⟩ with
  | left =>
    cases hlast : χ ⟨c2, d2, d3, hc2d2, hd23⟩ with
    | left => exact hS4both hfirst hlast
    | right => exact hcaseLeft hfirst hlast
  | right =>
    cases hlast : χ ⟨c2, d2, d3, hc2d2, hd23⟩ with
    | left => exact hcaseRight hfirst hlast
    | right => exact hcaseCaps hfirst hlast

end ErdosSzekeres
