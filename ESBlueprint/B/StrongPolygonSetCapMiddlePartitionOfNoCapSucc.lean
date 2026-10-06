import ErdosSzekeres.Decomposable

namespace ErdosSzekeres

/-- Canonical shape of a strong set: the cap-colored interior middles together with the extreme endpoints form a cap, the complement of those middles forms a cup, and avoiding a cap of size j+1 bounds the interior cap middles by j−2. Middle determinacy alone suffices; no OneChange hypothesis is needed.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn
@dangling-ok Reusable strong-set normal form for the approved R20 a≥5 tools; future multi-apex extensions and cup-layer arguments, no uniform a5 bound claimed -/
theorem strongPolygonSet_capMiddle_partition_of_no_cap_succ {n j : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {l r : Fin n}
    (hj : 2 ≤ j) (hl : l ∈ s) (hr : r ∈ s) (hlr : l < r)
    (hmin : ∀ x ∈ s, l ≤ x) (hmax : ∀ x ∈ s, x ≤ r)
    (hstrong : IsStrongPolygonSet χ s) (hnoCap : ¬ContainsCapSet χ s (j + 1)) :
    let capMiddle := s.filter (fun x => l < x ∧ x < r ∧ CupCap.totalColor χ l x r = Turn.right)
    capMiddle.card ≤ j - 2 ∧
      IsCupSet χ (s.filter (fun x => x ∉ capMiddle)) ∧
      IsCapSet χ (insert l (insert r capMiddle)) := by
  classical
  let B := s.filter (fun x => l < x ∧ x < r ∧ CupCap.totalColor χ l x r = Turn.right)
  let A := insert l (insert r B)
  change B.card ≤ j - 2 ∧ IsCupSet χ (s.filter (fun x => x ∉ B)) ∧ IsCapSet χ A
  have hmiddle := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hstrong
  have hBsub : B ⊆ s := Finset.filter_subset _ _
  have bounds (x : Fin n) (hx : x ∈ B) : l < x ∧ x < r := by
    exact ⟨(Finset.mem_filter.mp hx).2.1, (Finset.mem_filter.mp hx).2.2.1⟩
  have capTurn (x : Fin n) (hx : x ∈ B) (hlx : l < x) (hxr : x < r) :
      χ ⟨l, x, r, hlx, hxr⟩ = Turn.right := by
    have hcol := (Finset.mem_filter.mp hx).2.2.2
    rw [CupCap.totalColor_of_lt χ hlx hxr] at hcol
    exact hcol
  have hlNot : l ∉ B := fun hmem => (lt_irrefl l) (bounds l hmem).1
  have hrNot : r ∉ B := fun hmem => (lt_irrefl r) (bounds r hmem).2
  have hlNotInsert : l ∉ insert r B := by simp [hlNot, ne_of_lt hlr]
  have hAsub : A ⊆ s :=
    Finset.insert_subset_iff.mpr ⟨hl, Finset.insert_subset_iff.mpr ⟨hr, hBsub⟩⟩
  have hAcard : A.card = B.card + 2 := by
    simp only [A, Finset.card_insert_of_notMem hlNotInsert,
      Finset.card_insert_of_notMem hrNot]
  have hAcap : IsCapSet χ A := by
    intro t hi hj hk
    have hiS := hAsub hi
    have hjS := hAsub hj
    have hkS := hAsub hk
    have hlj : l < t.j := (hmin t.i hiS).trans_lt t.hij
    have hjr : t.j < r := t.hjk.trans_le (hmax t.k hkS)
    have hjB : t.j ∈ B := by
      simpa [A, ne_of_gt hlj, ne_of_lt hjr] using hj
    change χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ = Turn.right
    exact (hmiddle t.hij hlj t.hjk hjr hiS hl hjS hkS hr).trans
      (capTurn t.j hjB hlj hjr)
  have hAcardBound : A.card ≤ j := by
    by_contra hbig
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
      (by omega : j + 1 ≤ A.card)
    exact hnoCap ⟨T, hTsub.trans hAsub, hTcard,
      FinsetPolygon.IsCapSet.mono hAcap hTsub⟩
  refine ⟨by omega, ?_, hAcap⟩
  intro t hi hj hk
  obtain ⟨hiS, _⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjS, hjNot⟩ := Finset.mem_filter.mp hj
  obtain ⟨hkS, _⟩ := Finset.mem_filter.mp hk
  have hlj : l < t.j := (hmin t.i hiS).trans_lt t.hij
  have hjr : t.j < r := t.hjk.trans_le (hmax t.k hkS)
  have hleft : χ ⟨l, t.j, r, hlj, hjr⟩ = Turn.left := by
    cases hcol : χ ⟨l, t.j, r, hlj, hjr⟩ with
    | left => rfl
    | right =>
        exact False.elim (hjNot (Finset.mem_filter.mpr ⟨hjS, hlj, hjr,
          (CupCap.totalColor_of_lt χ hlj hjr).trans hcol⟩))
  change χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ = Turn.left
  exact (hmiddle t.hij hlj t.hjk hjr hiS hl hjS hkS hr).trans hleft

end ErdosSzekeres
