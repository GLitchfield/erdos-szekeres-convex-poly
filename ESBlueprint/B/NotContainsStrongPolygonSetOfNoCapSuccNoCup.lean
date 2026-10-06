import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- A support avoiding a(j+1)-cap and a u-cup avoids a strong polygon of u+j-2 points, for j,u at least two and without OneChange. Canonical cap-colored interiors consume at most j-2 vertices and leave a forbidden u-cup. This makes the a5 individual-side polygon bound automatic and isolates the crossing-set obstruction.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn
@dangling-ok Approved R20 reusable strong-set size interpretation for all cap bounds; proves why a5 polygon-dependent savings must involve crossing sets. -/
theorem notContainsStrongPolygonSet_of_no_capSucc_no_cup {n j u : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hj : 2 ≤ j) (hu : 2 ≤ u)
    (hnoCap : ¬ContainsCapSet χ s (j + 1)) (hnoCup : ¬ContainsCupSet χ s u) :
    ¬ContainsStrongPolygonSet χ s (u + j - 2) := by
  classical
  have shape {n j : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {l r : Fin n}
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
  intro ⟨polygon, hsub, hcard, hstrong⟩
  have hpositive : 0 < polygon.card := by omega
  have hne : polygon.Nonempty := Finset.card_pos.mp hpositive
  let l := polygon.min' hne
  let r := polygon.max' hne
  have hl : l ∈ polygon := polygon.min'_mem hne
  have hr : r ∈ polygon := polygon.max'_mem hne
  have hlr : l < r := polygon.min'_lt_max'_of_card (by omega)
  have hmin : ∀ x ∈ polygon, l ≤ x := by
    intro x hx
    exact polygon.min'_le x hx
  have hmax : ∀ x ∈ polygon, x ≤ r := by
    intro x hx
    exact polygon.le_max' x hx
  have hnoCapPolygon : ¬ContainsCapSet χ polygon (j + 1) := by
    intro ⟨T, hTsub, hTcard, hTcap⟩
    exact hnoCap ⟨T, hTsub.trans hsub, hTcard, hTcap⟩
  let B := polygon.filter (fun x => l < x ∧ x < r ∧ CupCap.totalColor χ l x r = Turn.right)
  let cup := polygon.filter (fun x => x ∉ B)
  have hshape := shape (χ := χ) (s := polygon) (j := j) (l := l) (r := r)
    hj hl hr hlr hmin hmax hstrong hnoCapPolygon
  change B.card ≤ j - 2 ∧ IsCupSet χ cup ∧ IsCapSet χ (insert l (insert r B)) at hshape
  obtain ⟨hBbound, hcup, _⟩ := hshape
  have hBsub : B ⊆ polygon := Finset.filter_subset _ _
  have hcupSub : cup ⊆ polygon := Finset.filter_subset _ _
  have hpartition : cup.card + B.card = u + j - 2 := by
    simpa only [cup, Finset.sdiff_eq_filter, hcard] using
      Finset.card_sdiff_add_card_eq_card hBsub
  have hcupCard : u ≤ cup.card := by omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcupCard
  exact hnoCup ⟨T, hTsub.trans (hcupSub.trans hsub), hTcard,
    FinsetPolygon.IsCupSet.mono hcup hTsub⟩


end ErdosSzekeres
