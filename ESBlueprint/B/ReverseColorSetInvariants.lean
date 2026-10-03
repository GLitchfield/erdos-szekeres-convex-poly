import ErdosSzekeres.StructuralChargingTransport

namespace ErdosSzekeres

/-- Order reversal preserves one-change, cups, caps, strong polygons, their prescribed-size containment, deep-below splits with unchanged lower/upper labels, and recursive decomposability on arbitrary finite sets. Fin.rev involution supplies both directions and lets mirrored root cases reuse one proof.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem reverseColor_set_invariants {n : ℕ} (χ : TripleColoring n) : (∀ s : Finset (Fin n), OneChangeOn χ s ↔ OneChangeOn (reverseColor χ) (s.image Fin.rev)) ∧ (∀ s : Finset (Fin n), IsCupSet χ s ↔ IsCupSet (reverseColor χ) (s.image Fin.rev)) ∧ (∀ s : Finset (Fin n), IsCapSet χ s ↔ IsCapSet (reverseColor χ) (s.image Fin.rev)) ∧ (∀ s : Finset (Fin n), IsStrongPolygonSet χ s ↔ IsStrongPolygonSet (reverseColor χ) (s.image Fin.rev)) ∧ (∀ (s : Finset (Fin n)) (k : ℕ), ContainsCupSet χ s k ↔ ContainsCupSet (reverseColor χ) (s.image Fin.rev) k) ∧ (∀ (s : Finset (Fin n)) (k : ℕ), ContainsCapSet χ s k ↔ ContainsCapSet (reverseColor χ) (s.image Fin.rev) k) ∧ (∀ (s : Finset (Fin n)) (k : ℕ), ContainsStrongPolygonSet χ s k ↔ ContainsStrongPolygonSet (reverseColor χ) (s.image Fin.rev) k) ∧ (∀ A B : Finset (Fin n), HasDeepBelowSplit χ A B ↔ HasDeepBelowSplit (reverseColor χ) (A.image Fin.rev) (B.image Fin.rev)) ∧ (∀ s : Finset (Fin n), IsDecomposableOn χ s ↔ IsDecomposableOn (reverseColor χ) (s.image Fin.rev)) := by
  classical
  have hmem (A : Finset (Fin n)) (x : Fin n) : x ∈ A.image Fin.rev ↔ x.rev ∈ A := by
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      simpa using hy
    · intro hx
      exact Finset.mem_image.mpr ⟨x.rev, hx, by simp⟩
  have himage (A : Finset (Fin n)) : (A.image Fin.rev).image Fin.rev = A := by
    simp [Finset.image_image, Function.comp_def]
  have hcolor (ψ : TripleColoring n) : reverseColor (reverseColor ψ) = ψ := by
    funext t
    cases t
    simp [reverseColor, reverseOrderedTriple]
  have hmono (ψ : TripleColoring n) (A : Finset (Fin n)) (c : Turn)
      (h : ∀ t : OrderedTriple n, t.i ∈ A → t.j ∈ A → t.k ∈ A → ψ t = c) :
      ∀ t : OrderedTriple n, t.i ∈ A.image Fin.rev → t.j ∈ A.image Fin.rev →
        t.k ∈ A.image Fin.rev → reverseColor ψ t = c := by
    intro t hi hj hk
    have hout := h (reverseOrderedTriple t) ((hmem A t.k).mp hk)
      ((hmem A t.j).mp hj) ((hmem A t.i).mp hi)
    simpa [reverseColor, reverseOrderedTriple] using hout
  have hcup (ψ : TripleColoring n) (A : Finset (Fin n))
      (h : IsCupSet ψ A) : IsCupSet (reverseColor ψ) (A.image Fin.rev) :=
    hmono ψ A Turn.left h
  have hcap (ψ : TripleColoring n) (A : Finset (Fin n))
      (h : IsCapSet ψ A) : IsCapSet (reverseColor ψ) (A.image Fin.rev) :=
    hmono ψ A Turn.right h
  have hone (ψ : TripleColoring n) (A : Finset (Fin n))
      (h : OneChangeOn ψ A) : OneChangeOn (reverseColor ψ) (A.image Fin.rev) := by
    intro i j k l hij hjk hkl hi hj hk hl
    have hout := h (i := l.rev) (j := k.rev) (k := j.rev) (l := i.rev)
      (by simpa using hkl) (by simpa using hjk) (by simpa using hij)
      ((hmem A l).mp hl) ((hmem A k).mp hk) ((hmem A j).mp hj) ((hmem A i).mp hi)
    simpa [reverseColor, reverseOrderedTriple] using hout.reversed
  have hstrong (ψ : TripleColoring n) (A : Finset (Fin n))
      (h : IsStrongPolygonSet ψ A) : IsStrongPolygonSet (reverseColor ψ) (A.image Fin.rev) := by
    intro i j k l hij hjk hkl hi hj hk hl
    have hout := h (i := l.rev) (j := k.rev) (k := j.rev) (l := i.rev)
      (by simpa using hkl) (by simpa using hjk) (by simpa using hij)
      ((hmem A l).mp hl) ((hmem A k).mp hk) ((hmem A j).mp hj) ((hmem A i).mp hi)
    simpa [reverseColor, reverseOrderedTriple] using And.intro hout.2.symm hout.1.symm
  have hcontainsCup (ψ : TripleColoring n) (A : Finset (Fin n)) (k : ℕ)
      (h : ContainsCupSet ψ A k) : ContainsCupSet (reverseColor ψ) (A.image Fin.rev) k := by
    obtain ⟨C, hCA, hCcard, hCcup⟩ := h
    refine ⟨C.image Fin.rev, Finset.image_subset_image hCA, ?_, hcup ψ C hCcup⟩
    exact (Finset.card_image_of_injective _ Fin.rev_injective).trans hCcard
  have hcontainsCap (ψ : TripleColoring n) (A : Finset (Fin n)) (k : ℕ)
      (h : ContainsCapSet ψ A k) : ContainsCapSet (reverseColor ψ) (A.image Fin.rev) k := by
    obtain ⟨C, hCA, hCcard, hCcap⟩ := h
    refine ⟨C.image Fin.rev, Finset.image_subset_image hCA, ?_, hcap ψ C hCcap⟩
    exact (Finset.card_image_of_injective _ Fin.rev_injective).trans hCcard
  have hcontainsStrong (ψ : TripleColoring n) (A : Finset (Fin n)) (k : ℕ)
      (h : ContainsStrongPolygonSet ψ A k) :
      ContainsStrongPolygonSet (reverseColor ψ) (A.image Fin.rev) k := by
    obtain ⟨C, hCA, hCcard, hCstrong⟩ := h
    refine ⟨C.image Fin.rev, Finset.image_subset_image hCA, ?_, hstrong ψ C hCstrong⟩
    exact (Finset.card_image_of_injective _ Fin.rev_injective).trans hCcard
  have hdeep (ψ : TripleColoring n) (A B : Finset (Fin n))
      (h : HasDeepBelowSplit ψ A B) :
      HasDeepBelowSplit (reverseColor ψ) (A.image Fin.rev) (B.image Fin.rev) := by
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro x hxA hxB
      exact (Finset.disjoint_left.mp h.disjoint) ((hmem A x).mp hxA) ((hmem B x).mp hxB)
    · intro t hi hj hk hnotA hnotB
      have hU (x : Fin n) (hx : x ∈ A.image Fin.rev ∪ B.image Fin.rev) : x.rev ∈ A ∪ B := by
        rw [← Finset.image_union] at hx
        exact (hmem (A ∪ B) x).mp hx
      have hnA : ¬(t.k.rev ∈ A ∧ t.j.rev ∈ A ∧ t.i.rev ∈ A) := by
        rintro ⟨hkA, hjA, hiA⟩
        exact hnotA ⟨(hmem A t.i).mpr hiA, (hmem A t.j).mpr hjA, (hmem A t.k).mpr hkA⟩
      have hnB : ¬(t.k.rev ∈ B ∧ t.j.rev ∈ B ∧ t.i.rev ∈ B) := by
        rintro ⟨hkB, hjB, hiB⟩
        exact hnotB ⟨(hmem B t.i).mpr hiB, (hmem B t.j).mpr hjB, (hmem B t.k).mpr hkB⟩
      have hout := h.crossing (reverseOrderedTriple t) (hU _ hk) (hU _ hj) (hU _ hi) hnA hnB
      simpa only [reverseColor, reverseOrderedTriple, hmem] using hout
  have hdecomp (ψ : TripleColoring n) (A : Finset (Fin n))
      (h : IsDecomposableOn ψ A) : IsDecomposableOn (reverseColor ψ) (A.image Fin.rev) := by
    induction h with
    | singleton i => simpa using IsDecomposableOn.singleton (χ := reverseColor ψ) i.rev
    | @split lower upper hlower hupper hsplit ihlower ihupper =>
      simpa only [Finset.image_union] using
        IsDecomposableOn.split ihlower ihupper (hdeep ψ lower upper hsplit)
  have hiff (P : TripleColoring n → Finset (Fin n) → Prop)
      (hforward : ∀ ψ A, P ψ A → P (reverseColor ψ) (A.image Fin.rev)) :
      ∀ A, P χ A ↔ P (reverseColor χ) (A.image Fin.rev) := by
    intro A
    constructor
    · exact hforward χ A
    · intro h
      simpa only [hcolor, himage] using hforward (reverseColor χ) (A.image Fin.rev) h
  refine ⟨hiff OneChangeOn hone, hiff IsCupSet hcup, hiff IsCapSet hcap,
    hiff IsStrongPolygonSet hstrong, ?_, ?_, ?_, ?_, hiff IsDecomposableOn hdecomp⟩
  · intro A k
    exact hiff (fun ψ A ↦ ContainsCupSet ψ A k) (fun ψ A ↦ hcontainsCup ψ A k) A
  · intro A k
    exact hiff (fun ψ A ↦ ContainsCapSet ψ A k) (fun ψ A ↦ hcontainsCap ψ A k) A
  · intro A k
    exact hiff (fun ψ A ↦ ContainsStrongPolygonSet ψ A k) (fun ψ A ↦ hcontainsStrong ψ A k) A
  · intro A B
    constructor
    · exact hdeep χ A B
    · intro h
      simpa only [hcolor, himage] using hdeep (reverseColor χ) (A.image Fin.rev) (B.image Fin.rev) h

end ErdosSzekeres
