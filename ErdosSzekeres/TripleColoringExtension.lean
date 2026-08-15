module

public import ErdosSzekeres.StructuralCharging

@[expose] public section

/-!
# Extending an ordered triple coloring by its last vertex

The one-change constraints on `n + 1` vertices split exactly into the
constraints on the first `n` vertices and the constraints involving the last
vertex.  The latter are expressed using the colors of the three pairs in each
increasing triple of initial vertices.
-/

namespace ErdosSzekeres

noncomputable section

/-- The increasing embedding of the first `n` indices into `Fin (n + 1)`. -/
def finInitialOrderEmbedding (n : ℕ) : Fin n ↪o Fin (n + 1) :=
  Fin.castSuccOrderEmb

namespace TripleColoring

/-- The color of the triple formed by two initial vertices and the last vertex. -/
def lastPairColor {n : ℕ} (χ : TripleColoring (n + 1))
    (i j : Fin n) (hij : i < j) : Turn :=
  χ ⟨i.castSucc, j.castSucc, Fin.last n,
    Fin.castSucc_lt_castSucc_iff.mpr hij, Fin.castSucc_lt_last j⟩

end TripleColoring

/-- Every new four-vertex constraint involving the last vertex is allowed. -/
def LastExtensionCompatible {n : ℕ} (χ : TripleColoring (n + 1)) : Prop :=
  ∀ {i j k : Fin n}, (hij : i < j) → (hjk : j < k) →
    TurnSequenceAllowed
      (χ.restrict (finInitialOrderEmbedding n) ⟨i, j, k, hij, hjk⟩)
      (χ.lastPairColor i j hij)
      (χ.lastPairColor i k (hij.trans hjk))
      (χ.lastPairColor j k hjk)

/-- The one-change law on `n + 1` vertices is exactly the old law together
with the constraints introduced by the last vertex. -/
theorem oneChangeOn_univ_succ_iff {n : ℕ} (χ : TripleColoring (n + 1)) :
    OneChangeOn χ Finset.univ ↔
      OneChangeOn (χ.restrict (finInitialOrderEmbedding n)) Finset.univ ∧
        LastExtensionCompatible χ := by
  constructor
  · intro hχ
    constructor
    · intro i j k l hij hjk hkl _ _ _ _
      have h := hχ
        (Fin.castSucc_lt_castSucc_iff.mpr hij)
        (Fin.castSucc_lt_castSucc_iff.mpr hjk)
        (Fin.castSucc_lt_castSucc_iff.mpr hkl)
        (by simp) (by simp) (by simp) (by simp)
      simpa [TripleColoring.restrict, OrderedTriple.map,
        finInitialOrderEmbedding] using h
    · intro i j k hij hjk
      have h := hχ
        (Fin.castSucc_lt_castSucc_iff.mpr hij)
        (Fin.castSucc_lt_castSucc_iff.mpr hjk)
        (Fin.castSucc_lt_last k)
        (by simp) (by simp) (by simp) (by simp)
      simpa [LastExtensionCompatible, TripleColoring.lastPairColor,
        TripleColoring.restrict, OrderedTriple.map,
        finInitialOrderEmbedding] using h
  · rintro ⟨hinit, hlast⟩
    intro i j k l hij hjk hkl _ _ _ _
    by_cases hl : l = Fin.last n
    · subst l
      have hkLast : k ≠ Fin.last n := ne_of_lt hkl
      have hjLast : j ≠ Fin.last n := ne_of_lt (hjk.trans hkl)
      have hiLast : i ≠ Fin.last n := ne_of_lt (hij.trans (hjk.trans hkl))
      obtain ⟨i', hi⟩ := Fin.eq_castSucc_of_ne_last hiLast
      obtain ⟨j', hj⟩ := Fin.eq_castSucc_of_ne_last hjLast
      obtain ⟨k', hk⟩ := Fin.eq_castSucc_of_ne_last hkLast
      subst i
      subst j
      subst k
      have hij' : i' < j' := Fin.castSucc_lt_castSucc_iff.mp hij
      have hjk' : j' < k' := Fin.castSucc_lt_castSucc_iff.mp hjk
      simpa [LastExtensionCompatible, TripleColoring.lastPairColor,
        TripleColoring.restrict, OrderedTriple.map,
        finInitialOrderEmbedding] using hlast hij' hjk'
    · have hlLast : l < Fin.last n := Fin.lt_last_iff_ne_last.mpr hl
      have hkLast : k ≠ Fin.last n := ne_of_lt (hkl.trans hlLast)
      have hjLast : j ≠ Fin.last n := ne_of_lt (hjk.trans (hkl.trans hlLast))
      have hiLast : i ≠ Fin.last n :=
        ne_of_lt (hij.trans (hjk.trans (hkl.trans hlLast)))
      obtain ⟨i', hi⟩ := Fin.eq_castSucc_of_ne_last hiLast
      obtain ⟨j', hj⟩ := Fin.eq_castSucc_of_ne_last hjLast
      obtain ⟨k', hk⟩ := Fin.eq_castSucc_of_ne_last hkLast
      obtain ⟨l', hl'⟩ := Fin.eq_castSucc_of_ne_last hl
      subst i
      subst j
      subst k
      subst l
      have hij' : i' < j' := Fin.castSucc_lt_castSucc_iff.mp hij
      have hjk' : j' < k' := Fin.castSucc_lt_castSucc_iff.mp hjk
      have hkl' : k' < l' := Fin.castSucc_lt_castSucc_iff.mp hkl
      have h := hinit hij' hjk' hkl' (by simp) (by simp) (by simp) (by simp)
      simpa [TripleColoring.restrict, OrderedTriple.map,
        finInitialOrderEmbedding] using h

end

end ErdosSzekeres

end
