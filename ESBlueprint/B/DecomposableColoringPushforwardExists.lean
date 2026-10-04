import ErdosSzekeres.SynchronizedFiveFanFin11WindowTransport

namespace ErdosSzekeres

/-- Every triple coloring extends along an increasing index embedding to an ambient coloring with exact restriction, preserving decomposable image supports, cup and cap predicates, strong-polygon existence at every size, and support cardinalities.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.containsStrongPolygonSet_image_restrict_iff
@dangling-ok General Q3 bridge from independent ordered child domains to the fixed ambient supports used by profile gluing; also needed to embed the smaller child in the general Q4 two-cap family construction. No closed maximum or endpoint-loss invariant is asserted. -/
theorem decomposable_coloring_pushforward_exists {m n : ℕ} (χ : TripleColoring m) (f : Fin m ↪o Fin n) : ∃ ψ : TripleColoring n, ψ.restrict f = χ ∧ (∀ S : Finset (Fin m), IsDecomposableOn χ S → IsDecomposableOn ψ (S.image f)) ∧ (∀ S : Finset (Fin m), IsCupSet χ S ↔ IsCupSet ψ (S.image f)) ∧ (∀ S : Finset (Fin m), IsCapSet χ S ↔ IsCapSet ψ (S.image f)) ∧ (∀ (S : Finset (Fin m)) (k : ℕ), ContainsStrongPolygonSet χ S k ↔ ContainsStrongPolygonSet ψ (S.image f) k) ∧ (∀ S : Finset (Fin m), (S.image f).card = S.card) := by
  classical
  have hmap : Function.Injective (fun t : OrderedTriple m ↦ t.map f) := by
    intro a b hab
    have hi : a.i = b.i := f.injective (congrArg OrderedTriple.i hab)
    have hj : a.j = b.j := f.injective (congrArg OrderedTriple.j hab)
    have hk : a.k = b.k := f.injective (congrArg OrderedTriple.k hab)
    cases a
    cases b
    cases hi
    cases hj
    cases hk
    rfl
  let ψ : TripleColoring n :=
    Function.extend (fun t : OrderedTriple m ↦ t.map f) χ (fun _ ↦ Turn.left)
  have hagree (t : OrderedTriple m) : ψ (t.map f) = χ t :=
    hmap.extend_apply χ (fun _ ↦ Turn.left) t
  have hrestrict : ψ.restrict f = χ := by
    funext t
    exact hagree t
  have hmem (S : Finset (Fin m)) (a : Fin m) : f a ∈ S.image f ↔ a ∈ S := by
    simp [Finset.mem_image, f.injective.eq_iff]
  have hdeep (L U : Finset (Fin m)) (hd : HasDeepBelowSplit χ L U) :
      HasDeepBelowSplit ψ (L.image f) (U.image f) := by
    refine ⟨(Finset.disjoint_image f.injective).mpr hd.disjoint, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnL hnU
    rw [← Finset.image_union] at hi hj hk
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hk
    have hnotL : ¬ (i' ∈ L ∧ j' ∈ L ∧ k' ∈ L) := by
      rintro ⟨hiL, hjL, hkL⟩
      exact hnL ⟨(hmem L i').mpr hiL, (hmem L j').mpr hjL, (hmem L k').mpr hkL⟩
    have hnotU : ¬ (i' ∈ U ∧ j' ∈ U ∧ k' ∈ U) := by
      rintro ⟨hiU, hjU, hkU⟩
      exact hnU ⟨(hmem U i').mpr hiU, (hmem U j').mpr hjU, (hmem U k').mpr hkU⟩
    let t : OrderedTriple m :=
      ⟨i', j', k', f.lt_iff_lt.mp hij, f.lt_iff_lt.mp hjk⟩
    change ψ (t.map f) = if f j' ∈ L.image f then Turn.left else Turn.right
    rw [hagree]
    simpa only [hmem] using hd.crossing t hi' hj' hk' hnotL hnotU
  have hdecomp (S : Finset (Fin m)) (hd : IsDecomposableOn χ S) :
      IsDecomposableOn ψ (S.image f) := by
    induction hd with
    | singleton i => simpa using IsDecomposableOn.singleton (χ := ψ) (f i)
    | @split L U hL hU hd ihL ihU =>
      simpa only [Finset.image_union] using
        IsDecomposableOn.split ihL ihU (hdeep L U hd)
  have hmono (S : Finset (Fin m)) (c : Turn) :
      (∀ t : OrderedTriple m, t.i ∈ S → t.j ∈ S → t.k ∈ S → χ t = c) ↔
      (∀ t : OrderedTriple n,
        t.i ∈ S.image f → t.j ∈ S.image f → t.k ∈ S.image f → ψ t = c) := by
    constructor
    · intro h
      rintro ⟨i, j, k, hij, hjk⟩ hi hj hk
      obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hk
      let t : OrderedTriple m :=
        ⟨i', j', k', f.lt_iff_lt.mp hij, f.lt_iff_lt.mp hjk⟩
      change ψ (t.map f) = c
      rw [hagree]
      exact h t hi' hj' hk'
    · intro h t hi hj hk
      rw [← hagree t]
      exact h (t.map f) ((hmem S t.i).mpr hi)
        ((hmem S t.j).mpr hj) ((hmem S t.k).mpr hk)
  refine ⟨ψ, hrestrict, hdecomp, ?_, ?_, ?_, ?_⟩
  · intro S
    exact hmono S Turn.left
  · intro S
    exact hmono S Turn.right
  · intro S k
    simpa only [hrestrict] using
      containsStrongPolygonSet_image_restrict_iff (k := k) ψ f S
  · intro S
    exact Finset.card_image_of_injective S f.injective


end ErdosSzekeres
