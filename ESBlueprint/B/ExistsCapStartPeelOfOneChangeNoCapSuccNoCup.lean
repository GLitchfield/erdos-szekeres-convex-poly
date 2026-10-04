import ESBlueprint.B.MonochromaticSetInsertMaxOfOneChange
import ESBlueprint.B.MonochromaticSetInsertMinOfOneChange

namespace ErdosSzekeres

/-- The first points of c-caps peel a one-change set avoiding (c+1)-caps and v-cups into a c-cap-free complement and a start set avoiding (v-1)-cups. This common extension argument underlies the audited cap-six Z-lemmas.
@node
@ws B
@kind formalization
@dangling-ok R23 audited (6,k-2,k) gate lemma layer -/
theorem exists_capStartPeel_of_oneChange_no_capSucc_no_cup {n c v : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} (hc : 2 ≤ c) (hv : 2 ≤ v) (hone : OneChangeOn χ s) (hnoCap : ¬ContainsCapSet χ s (c + 1)) (hnoCup : ¬ContainsCupSet χ s v) : ∃ Z : Finset (Fin n), Z ⊆ s ∧ (∀ x : Fin n, x ∈ Z ↔ x ∈ s ∧ ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = c ∧ IsCapSet χ C ∧ x ∈ C ∧ ∀ y ∈ C, x ≤ y) ∧ ¬ContainsCapSet χ (s \ Z) c ∧ ¬ContainsCupSet χ Z (v - 1) := by
  classical
  let Z := s.filter (fun x ↦ ∃ C : Finset (Fin n),
    C ⊆ s ∧ C.card = c ∧ IsCapSet χ C ∧ x ∈ C ∧ ∀ y ∈ C, x ≤ y)
  have hZsub : Z ⊆ s := Finset.filter_subset _ _
  have hZmem : ∀ x : Fin n, x ∈ Z ↔ x ∈ s ∧ ∃ C : Finset (Fin n),
      C ⊆ s ∧ C.card = c ∧ IsCapSet χ C ∧ x ∈ C ∧ ∀ y ∈ C, x ≤ y := by
    intro x
    exact Finset.mem_filter
  have hrestSub : s \ Z ⊆ s := Finset.sdiff_subset
  have hrestNoCap : ¬ContainsCapSet χ (s \ Z) c := by
    rintro ⟨C, hCsub, hCcard, hCcap⟩
    have hCne : C.Nonempty := by
      rw [← Finset.card_pos, hCcard]
      omega
    let x := C.min' hCne
    have hxC : x ∈ C := Finset.min'_mem _ _
    have hxrest := Finset.mem_sdiff.mp (hCsub hxC)
    apply hxrest.2
    refine (hZmem x).mpr ⟨hxrest.1, C, hCsub.trans hrestSub,
      hCcard, hCcap, hxC, ?_⟩
    intro y hy
    exact Finset.min'_le _ y hy
  have hsmall : ∀ A : Finset (Fin n), A.card ≤ 2 → IsCupSet χ A := by
    intro A hA t hi hj hk
    exfalso
    have hsub : ({t.i, t.j, t.k} : Finset (Fin n)) ⊆ A := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hi, hj, hk⟩
    have hcard : ({t.i, t.j, t.k} : Finset (Fin n)).card = 3 := by
      simp [ne_of_lt t.hij, ne_of_lt t.hjk, ne_of_lt (t.hij.trans t.hjk)]
    have := Finset.card_le_card hsub
    omega
  refine ⟨Z, hZsub, hZmem, hrestNoCap, ?_⟩
  rintro ⟨P, hPsub, hPcard, hPcup⟩
  have hPne : P.Nonempty := by
    rw [← Finset.card_pos, hPcard]
    omega
  let z := P.max' hPne
  have hzP : z ∈ P := Finset.max'_mem _ _
  have hPmax : ∀ y ∈ P, y ≤ z := by
    intro y hy
    exact Finset.le_max' _ y hy
  obtain ⟨_, C, hCsub, hCcard, hCcap, hzC, hCmin⟩ :=
    (hZmem z).mp (hPsub hzP)
  have hCrest : (C.erase z).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hzC, hCcard]
    omega
  let a := (C.erase z).min' hCrest
  have haErase : a ∈ C.erase z := Finset.min'_mem _ _
  have haC : a ∈ C := (Finset.mem_erase.mp haErase).2
  have hza : z < a := by
    have := hCmin a haC
    have := (Finset.mem_erase.mp haErase).1
    omega
  have hCnext : ∀ y ∈ C, z < y → a ≤ y := by
    intro y hy hzy
    exact Finset.min'_le _ y (Finset.mem_erase.mpr ⟨ne_of_gt hzy, hy⟩)
  have hPsubS : P ⊆ s := hPsub.trans hZsub
  have haNotP : a ∉ P := by
    intro haP
    have := hPmax a haP
    omega
  have hnewSub : insert a P ⊆ s :=
    Finset.insert_subset_iff.mpr ⟨hCsub haC, hPsubS⟩
  have hnewCard : (insert a P).card = v := by
    rw [Finset.card_insert_of_notMem haNotP, hPcard]
    omega
  by_cases hvTwo : v = 2
  · exact hnoCup ⟨insert a P, hnewSub, hnewCard, hsmall _ (by omega)⟩
  have hPrest : (P.erase z).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hzP, hPcard]
    omega
  let b := (P.erase z).max' hPrest
  have hbErase : b ∈ P.erase z := Finset.max'_mem _ _
  have hbP : b ∈ P := (Finset.mem_erase.mp hbErase).2
  have hbz : b < z := by
    have := hPmax b hbP
    have := (Finset.mem_erase.mp hbErase).1
    omega
  have hPprev : ∀ y ∈ P, y < z → y ≤ b := by
    intro y hy hyz
    exact Finset.le_max' _ y (Finset.mem_erase.mpr ⟨ne_of_lt hyz, hy⟩)
  cases hturn : χ ⟨b, z, a, hbz, hza⟩ with
  | left =>
    have hnewCup : IsCupSet χ (insert a P) :=
      monochromaticSet_insert_max_of_oneChange hbP hzP hbz hza hPmax hPprev
        hPcup (hone.mono hnewSub) hturn
    exact hnoCup ⟨insert a P, hnewSub, hnewCard, hnewCup⟩
  | right =>
    have hbNotC : b ∉ C := by
      intro hbC
      have := hCmin b hbC
      omega
    have hcapSub : insert b C ⊆ s :=
      Finset.insert_subset_iff.mpr ⟨hPsubS hbP, hCsub⟩
    have hnewCap : IsCapSet χ (insert b C) :=
      monochromaticSet_insert_min_of_oneChange hzC haC hza hbz hCmin hCnext
        hCcap (hone.mono hcapSub) hturn
    apply hnoCap
    refine ⟨insert b C, hcapSub, ?_, hnewCap⟩
    rw [Finset.card_insert_of_notMem hbNotC, hCcard]


end ErdosSzekeres
