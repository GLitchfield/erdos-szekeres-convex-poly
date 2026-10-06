import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- Cup killing outside the side three-cap boundaries: a cup of at least three vertices whose left points end left three-caps and whose right points start right three-caps extends by one ambient point. Its first or last consecutive side pair forces an extending cup turn, since the opposite turn would make a forbidden side four-cap.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.TurnSequenceAllowed.all_eq_of_outer_eq, ErdosSzekeres.isMonochromaticChain_finFour_of_outer_eq
@dangling-ok Approved R20 L3 formalization: local cup hitting explains the remaining strong-set shape; tight coupled E selection remains open. -/
theorem existsCupExtension_of_side_three_caps {n : ℕ} {χ : TripleColoring n} {left right C : Finset (Fin n)}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hone : OneChangeOn χ (left ∪ right))
    (hnoLeft : ¬ContainsCapSet χ left 4)
    (hnoRight : ¬ContainsCapSet χ right 4)
    (hCsub : C ⊆ left ∪ right) (hCcup : IsCupSet χ C) (hcard : 3 ≤ C.card)
    (hendCap : ∀ x ∈ C, x ∈ left →
      ∃ a ∈ left, ∃ b ∈ left, ∃ hab : a < b, ∃ hbx : b < x,
        χ ⟨a, b, x, hab, hbx⟩ = Turn.right)
    (hstartCap : ∀ x ∈ C, x ∈ right →
      ∃ a ∈ right, ∃ b ∈ right, ∃ hxa : x < a, ∃ hab : a < b,
        χ ⟨x, a, b, hxa, hab⟩ = Turn.right) :
    ∃ p ∈ left ∪ right, p ∉ C ∧ IsCupSet χ (insert p C) ∧
      (insert p C).card = C.card + 1 := by
  classical
  have append {s C : Finset (Fin n)} {w x y : Fin n}
      (hone : OneChangeOn χ s)
      (hCsub : C ⊆ s) (hcup : IsCupSet χ C) (hx : x ∈ C) (hw : w ∈ C)
      (hwx : w < x) (hxy : x < y) (hy : y ∈ s)
      (hend : ∀ a ∈ C, a ≤ x) (hprev : ∀ a ∈ C, a < x → a ≤ w)
      (hturn : χ ⟨w, x, y, hwx, hxy⟩ = Turn.left) :
      IsCupSet χ (insert y C) := by
    have endpointTurn (a : Fin n) (ha : a ∈ C) (hax : a < x) :
        χ ⟨a, x, y, hax, hxy⟩ = Turn.left := by
      rcases eq_or_lt_of_le (hprev a ha hax) with rfl | haw
      · exact hturn
      · have hfirst := hcup ⟨a, w, x, haw, hwx⟩ ha hw hx
        have hseq := hone haw hwx hxy (hCsub ha) (hCsub hw) (hCsub hx) hy
        have hall := hseq.all_eq_of_outer_eq (hfirst.trans hturn.symm)
        exact hall.2.2.trans hturn
    intro t hi hj hk
    change χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ = Turn.left
    by_cases hky : t.k = y
    · have hiNot : t.i ≠ y := by
        rw [← hky]
        exact ne_of_lt (t.hij.trans t.hjk)
      have hjNot : t.j ≠ y := by
        rw [← hky]
        exact ne_of_lt t.hjk
      have hiC : t.i ∈ C := by simpa [hiNot] using hi
      have hjC : t.j ∈ C := by simpa [hjNot] using hj
      rcases eq_or_lt_of_le (hend t.j hjC) with hjx | hjx
      · have hix : t.i < x := by simpa [hjx] using t.hij
        simpa [hky, hjx] using endpointTurn t.i hiC hix
      · have hfirst := hcup ⟨t.i, t.j, x, t.hij, hjx⟩ hiC hjC hx
        have hlast := endpointTurn t.j hjC hjx
        have hseq := hone t.hij hjx hxy (hCsub hiC) (hCsub hjC) (hCsub hx) hy
        have hall := hseq.all_eq_of_outer_eq (hfirst.trans hlast.symm)
        simpa [hky] using hall.1.symm.trans hfirst
    · have hkC : t.k ∈ C := by simpa [hky] using hk
      have hkyLt : t.k < y := (hend t.k hkC).trans_lt hxy
      have hiC : t.i ∈ C := by
        simpa [ne_of_lt (t.hij.trans (t.hjk.trans hkyLt))] using hi
      have hjC : t.j ∈ C := by simpa [ne_of_lt (t.hjk.trans hkyLt)] using hj
      exact hcup t hiC hjC hkC

  have prepend {s C : Finset (Fin n)} {y x w : Fin n}
      (hone : OneChangeOn χ s)
      (hCsub : C ⊆ s) (hcup : IsCupSet χ C) (hx : x ∈ C) (hw : w ∈ C)
      (hyx : y < x) (hxw : x < w) (hy : y ∈ s)
      (hstart : ∀ a ∈ C, x ≤ a) (hnext : ∀ a ∈ C, x < a → w ≤ a)
      (hturn : χ ⟨y, x, w, hyx, hxw⟩ = Turn.left) :
      IsCupSet χ (insert y C) := by
    have endpointTurn (a : Fin n) (ha : a ∈ C) (hxa : x < a) :
        χ ⟨y, x, a, hyx, hxa⟩ = Turn.left := by
      rcases eq_or_lt_of_le (hnext a ha hxa) with rfl | hwa
      · exact hturn
      · have hlast := hcup ⟨x, w, a, hxw, hwa⟩ hx hw ha
        have hseq := hone hyx hxw hwa hy (hCsub hx) (hCsub hw) (hCsub ha)
        have hall := hseq.all_eq_of_outer_eq (hturn.trans hlast.symm)
        exact hall.1.symm.trans hturn
    intro t hi hj hk
    change χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ = Turn.left
    by_cases hiy : t.i = y
    · have hjNot : t.j ≠ y := by
        rw [← hiy]
        exact ne_of_gt t.hij
      have hkNot : t.k ≠ y := by
        rw [← hiy]
        exact ne_of_gt (t.hij.trans t.hjk)
      have hjC : t.j ∈ C := by simpa [hjNot] using hj
      have hkC : t.k ∈ C := by simpa [hkNot] using hk
      rcases eq_or_lt_of_le (hstart t.j hjC) with hxj | hxj
      · have hxk : x < t.k := by simpa [hxj] using t.hjk
        simpa [hiy, hxj] using endpointTurn t.k hkC hxk
      · have hfirst := endpointTurn t.j hjC hxj
        have hlast := hcup ⟨x, t.j, t.k, hxj, t.hjk⟩ hx hjC hkC
        have hseq := hone hyx hxj t.hjk hy (hCsub hx) (hCsub hjC) (hCsub hkC)
        have hall := hseq.all_eq_of_outer_eq (hfirst.trans hlast.symm)
        simpa [hiy] using hall.2.2.trans hlast
    · have hiC : t.i ∈ C := by simpa [hiy] using hi
      have hyiLt : y < t.i := hyx.trans_le (hstart t.i hiC)
      have hjC : t.j ∈ C := by simpa [ne_of_gt (hyiLt.trans t.hij)] using hj
      have hkC : t.k ∈ C := by
        simpa [ne_of_gt (hyiLt.trans (t.hij.trans t.hjk))] using hk
      exact hcup t hiC hjC hkC

  have fourCap {s : Finset (Fin n)} {a b c d : Fin n}
      (hone : OneChangeOn χ s)
      (hab : a < b) (hbc : b < c) (hcd : c < d)
      (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
      (hfirst : χ ⟨a, b, c, hab, hbc⟩ = Turn.right)
      (hlast : χ ⟨b, c, d, hbc, hcd⟩ = Turn.right) :
      ContainsCapSet χ s 4 := by
    let f : Fin 4 ↪o Fin n := OrderEmbedding.ofStrictMono ![a, b, c, d] (by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      fin_cases i
      · simpa using hab
      · simpa using hbc
      · simpa using hcd)
    have hsub : Finset.univ.image f ⊆ s := by
      intro z hz
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
      obtain ⟨i, rfl⟩ := hz
      fin_cases i
      · simpa [f] using ha
      · simpa [f] using hb
      · simpa [f] using hc
      · simpa [f] using hd
    refine ⟨Finset.univ.image f, hsub, ?_, ?_⟩
    · simpa using Finset.card_image_of_injective Finset.univ f.injective
    · exact FinsetPolygon.IsCap.image (isMonochromaticChain_finFour_of_outer_eq f
        (hone.mono hsub) (by simpa [f] using hfirst) (by simpa [f] using hlast))

  let f : Fin C.card ↪o Fin n := C.orderEmbOfFin rfl
  let first : Fin C.card := ⟨0, by omega⟩
  let second : Fin C.card := ⟨1, by omega⟩
  let beforeLast : Fin C.card := ⟨C.card - 2, by omega⟩
  let last : Fin C.card := ⟨C.card - 1, by omega⟩
  have hfmem (i : Fin C.card) : f i ∈ C := C.orderEmbOfFin_mem rfl i
  have himage : Finset.univ.image f = C := by
    simpa [f] using C.image_orderEmbOfFin_univ rfl
  have repr {x : Fin n} (hx : x ∈ C) : ∃ i : Fin C.card, f i = x := by
    have hximage : x ∈ Finset.univ.image f := by simpa [himage] using hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hximage
    exact ⟨i, hi⟩
  have hfirstSecond : f first < f second := f.strictMono (by change 0 < 1; decide)
  have hbeforeLast : f beforeLast < f last := f.strictMono (by
    change C.card - 2 < C.card - 1
    omega)
  have hfirstMin : ∀ x ∈ C, f first ≤ x := by
    intro x hx
    obtain ⟨i, rfl⟩ := repr hx
    exact f.monotone (by change 0 ≤ i.val; exact Nat.zero_le _)
  have hsecondMin : ∀ x ∈ C, f first < x → f second ≤ x := by
    intro x hx hlt
    obtain ⟨i, rfl⟩ := repr hx
    have hi : first < i := f.lt_iff_lt.mp hlt
    change 0 < i.val at hi
    apply f.monotone
    change 1 ≤ i.val
    omega
  have hlastMax : ∀ x ∈ C, x ≤ f last := by
    intro x hx
    obtain ⟨i, rfl⟩ := repr hx
    apply f.monotone
    change i.val ≤ C.card - 1
    have hi := i.isLt
    omega
  have hbeforeLastMax : ∀ x ∈ C, x < f last → x ≤ f beforeLast := by
    intro x hx hlt
    obtain ⟨i, rfl⟩ := repr hx
    have hi : i < last := f.lt_iff_lt.mp hlt
    change i.val < C.card - 1 at hi
    apply f.monotone
    change i.val ≤ C.card - 2
    omega
  by_cases hsecondLeft : f second ∈ left
  · have hfirstLeft : f first ∈ left := by
      rcases Finset.mem_union.mp (hCsub (hfmem first)) with hleft | hright
      · exact hleft
      · exact False.elim ((lt_asymm hfirstSecond)
          (horder _ hsecondLeft _ hright))
    obtain ⟨w, hw, v, hv, hwv, hva, hcap⟩ :=
      hendCap (f first) (hfmem first) hfirstLeft
    have hvAmbient : v ∈ left ∪ right := Finset.mem_union_left right hv
    have hvNot : v ∉ C := by
      intro hvC
      exact (not_lt_of_ge (hfirstMin v hvC)) hva
    have hturn : χ ⟨v, f first, f second, hva, hfirstSecond⟩ = Turn.left := by
      cases hcol : χ ⟨v, f first, f second, hva, hfirstSecond⟩ with
      | left => rfl
      | right =>
          exact False.elim (hnoLeft (fourCap (s := left)
            (hone.mono Finset.subset_union_left) hwv hva hfirstSecond
            hw hv hfirstLeft hsecondLeft hcap hcol))
    refine ⟨v, hvAmbient, hvNot, ?_, ?_⟩
    · exact prepend hone hCsub hCcup (hfmem first) (hfmem second)
        hva hfirstSecond hvAmbient hfirstMin hsecondMin hturn
    · simp [hvNot]
  · have hsecondRight : f second ∈ right := by
      rcases Finset.mem_union.mp (hCsub (hfmem second)) with hleft | hright
      · exact False.elim (hsecondLeft hleft)
      · exact hright
    have laterRight {i : Fin C.card} (hge : second ≤ i) : f i ∈ right := by
      rcases Finset.mem_union.mp (hCsub (hfmem i)) with hleft | hright
      · exact False.elim ((not_lt_of_ge (f.monotone hge))
          (horder _ hleft _ hsecondRight))
      · exact hright
    have hbeforeLastRight : f beforeLast ∈ right := laterRight (by
      change 1 ≤ C.card - 2
      omega)
    have hlastRight : f last ∈ right := laterRight (by
      change 1 ≤ C.card - 1
      omega)
    obtain ⟨v, hv, w, hw, hlv, hvw, hcap⟩ :=
      hstartCap (f last) (hfmem last) hlastRight
    have hvAmbient : v ∈ left ∪ right := Finset.mem_union_right left hv
    have hvNot : v ∉ C := by
      intro hvC
      exact (not_lt_of_ge (hlastMax v hvC)) hlv
    have hturn : χ ⟨f beforeLast, f last, v, hbeforeLast, hlv⟩ = Turn.left := by
      cases hcol : χ ⟨f beforeLast, f last, v, hbeforeLast, hlv⟩ with
      | left => rfl
      | right =>
          exact False.elim (hnoRight (fourCap (s := right)
            (hone.mono Finset.subset_union_right) hbeforeLast hlv hvw
            hbeforeLastRight hlastRight hv hw hcol hcap))
    refine ⟨v, hvAmbient, hvNot, ?_, ?_⟩
    · exact append hone hCsub hCcup (hfmem last) (hfmem beforeLast)
        hbeforeLast hlv hvAmbient hlastMax hbeforeLastMax hturn
    · simp [hvNot]


end ErdosSzekeres
