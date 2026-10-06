import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- A cap turn a<b<c in a OneChange five-cap-free support forces extension of at least one outer cup to b: an ending cup at a or a starting cup at c, each of size at least two. Refusal of both gives a predecessor/successor five-cap.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.TurnSequenceAllowed.all_eq_of_outer_eq, ErdosSzekeres.isMonochromaticChain_finFive_of_consecutive
@dangling-ok Approved R20 reusable a5 structural tool explaining cross-gap layer compatibility through extension alternatives; coupled polygon deficiency remains open -/
theorem isCupSet_insert_or_insert_of_no_capFive {n : ℕ} {χ : TripleColoring n} {s C D : Finset (Fin n)} {a b c : Fin n}
    (hab : a < b) (hbc : b < c) (hone : OneChangeOn χ s)
    (hnoFive : ¬ContainsCapSet χ s 5)
    (hCsub : C ⊆ s) (hDsub : D ⊆ s) (hb : b ∈ s)
    (hCcup : IsCupSet χ C) (hDcup : IsCupSet χ D)
    (haC : a ∈ C) (hcD : c ∈ D)
    (hend : ∀ x ∈ C, x ≤ a) (hstart : ∀ x ∈ D, c ≤ x)
    (hCcard : 2 ≤ C.card) (hDcard : 2 ≤ D.card)
    (hturn : χ ⟨a, b, c, hab, hbc⟩ = Turn.right) :
    IsCupSet χ (insert b C) ∨ IsCupSet χ (insert b D) := by
  classical
  have append {C : Finset (Fin n)} {w x y : Fin n}
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
  have prepend {C : Finset (Fin n)} {y x w : Fin n}
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

  by_cases hleft : IsCupSet χ (insert b C)
  · exact Or.inl hleft
  by_cases hright : IsCupSet χ (insert b D)
  · exact Or.inr hright
  apply False.elim
  have hCdrop := Finset.card_erase_add_one haC
  have hCne : (C.erase a).Nonempty := Finset.card_pos.mp (by omega)
  let w := (C.erase a).max' hCne
  have hwErase : w ∈ C.erase a := Finset.max'_mem _ hCne
  obtain ⟨hwNe, hwC⟩ := Finset.mem_erase.mp hwErase
  have hwa : w < a := by
    have hle := hend w hwC
    omega
  have hprev : ∀ x ∈ C, x < a → x ≤ w := by
    intro x hx hxa
    exact Finset.le_max' _ x (Finset.mem_erase.mpr ⟨ne_of_lt hxa, hx⟩)
  have hfirst : χ ⟨w, a, b, hwa, hab⟩ = Turn.right := by
    cases hcol : χ ⟨w, a, b, hwa, hab⟩ with
    | right => rfl
    | left =>
        exact False.elim (hleft (append hCsub hCcup haC hwC hwa hab hb hend hprev hcol))
  have hDdrop := Finset.card_erase_add_one hcD
  have hDne : (D.erase c).Nonempty := Finset.card_pos.mp (by omega)
  let z := (D.erase c).min' hDne
  have hzErase : z ∈ D.erase c := Finset.min'_mem _ hDne
  obtain ⟨hzNe, hzD⟩ := Finset.mem_erase.mp hzErase
  have hcz : c < z := by
    have hle := hstart z hzD
    omega
  have hnext : ∀ x ∈ D, c < x → z ≤ x := by
    intro x hx hcx
    exact Finset.min'_le _ x (Finset.mem_erase.mpr ⟨ne_of_gt hcx, hx⟩)
  have hlast : χ ⟨b, c, z, hbc, hcz⟩ = Turn.right := by
    cases hcol : χ ⟨b, c, z, hbc, hcz⟩ with
    | right => rfl
    | left =>
        exact False.elim (hright (prepend hDsub hDcup hcD hzD hbc hcz hb hstart hnext hcol))
  let f : Fin 5 ↪o Fin n := OrderEmbedding.ofStrictMono ![w, a, b, c, z] (by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · simpa using hwa
    · simpa using hab
    · simpa using hbc
    · simpa using hcz)
  have hsub : Finset.univ.image f ⊆ s := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    fin_cases i
    · simpa [f] using hCsub hwC
    · simpa [f] using hCsub haC
    · simpa [f] using hb
    · simpa [f] using hDsub hcD
    · simpa [f] using hDsub hzD
  refine hnoFive ⟨Finset.univ.image f, hsub, ?_, ?_⟩
  · simpa using Finset.card_image_of_injective Finset.univ f.injective
  · exact FinsetPolygon.IsCap.image (isMonochromaticChain_finFive_of_consecutive f
      (hone.mono hsub) (by simpa [f] using hfirst)
      (by simpa [f] using hturn) (by simpa [f] using hlast))


end ErdosSzekeres
