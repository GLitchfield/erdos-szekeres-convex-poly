module

public import ErdosSzekeres.TripleColoringExtension

@[expose] public section

/-!
# Exact geometric extension by the rightmost point

This file retains the parent realization when a new rightmost point is added.
It does not assert that feasible extensions depend only on the parent's triple
coloring.
-/

namespace ErdosSzekeres

noncomputable section

/-- Exact geometric data for adjoining a rightmost point to a swept
configuration while realizing a prescribed coloring. -/
structure RightExtensionData {n : ℕ} (χ : TripleColoring (n + 1))
    (P : SweptConfiguration n) (q : Point 2) : Prop where
  right : ∀ i, P.point i 0 < q 0
  generalPosition : ∀ i j, i ≠ j →
    orientation (P.point i) (P.point j) q ≠ 0
  initialColoring :
    P.tripleColoring = χ.restrict (finInitialOrderEmbedding n)
  lastPairColor : ∀ i j (hij : i < j),
    (if 0 < orientation (P.point i) (P.point j) q then
      Turn.left
    else
      Turn.right) = χ.lastPairColor i j hij

/-- Adjoin the new point as the last point of a swept configuration. -/
def RightExtensionData.toSweptConfiguration {n : ℕ}
    {χ : TripleColoring (n + 1)} {P : SweptConfiguration n} {q : Point 2}
    (data : RightExtensionData χ P q) : SweptConfiguration (n + 1) where
  point := Fin.lastCases q P.point
  sweep_strictMono := by
    intro i j hij
    by_cases hj : j = Fin.last n
    · subst j
      have hi : i ≠ Fin.last n := ne_of_lt hij
      obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      simpa using data.right i'
    · have hjLast : j < Fin.last n := Fin.lt_last_iff_ne_last.mpr hj
      have hi : i ≠ Fin.last n := ne_of_lt (hij.trans hjLast)
      obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      obtain ⟨j', rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      simpa using P.sweep_strictMono (Fin.castSucc_lt_castSucc_iff.mp hij)
  generalPosition := by
    intro i j k hij hik hjk
    by_cases hi : i = Fin.last n
    · subst i
      have hjLast : j ≠ Fin.last n := hij.symm
      have hkLast : k ≠ Fin.last n := hik.symm
      obtain ⟨j', rfl⟩ := Fin.eq_castSucc_of_ne_last hjLast
      obtain ⟨k', rfl⟩ := Fin.eq_castSucc_of_ne_last hkLast
      have hjk' : j' ≠ k' := by
        intro h
        exact hjk (congrArg Fin.castSucc h)
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      change orientation q (P.point j') (P.point k') ≠ 0
      rw [orientation_cyclic']
      exact data.generalPosition j' k' hjk'
    · obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      by_cases hj : j = Fin.last n
      · subst j
        have hkLast : k ≠ Fin.last n := hjk.symm
        obtain ⟨k', rfl⟩ := Fin.eq_castSucc_of_ne_last hkLast
        have hik' : i' ≠ k' := by
          intro h
          exact hik (congrArg Fin.castSucc h)
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
        change orientation (P.point i') q (P.point k') ≠ 0
        rw [orientation_swap_last]
        exact neg_ne_zero.mpr (data.generalPosition i' k' hik')
      · obtain ⟨j', rfl⟩ := Fin.eq_castSucc_of_ne_last hj
        by_cases hk : k = Fin.last n
        · subst k
          have hij' : i' ≠ j' := by
            intro h
            exact hij (congrArg Fin.castSucc h)
          simpa using data.generalPosition i' j' hij'
        · obtain ⟨k', rfl⟩ := Fin.eq_castSucc_of_ne_last hk
          have hij' : i' ≠ j' := by
            intro h
            exact hij (congrArg Fin.castSucc h)
          have hik' : i' ≠ k' := by
            intro h
            exact hik (congrArg Fin.castSucc h)
          have hjk' : j' ≠ k' := by
            intro h
            exact hjk (congrArg Fin.castSucc h)
          simpa using P.generalPosition hij' hik' hjk'

@[simp] theorem RightExtensionData.toSweptConfiguration_point_castSucc
    {n : ℕ} {χ : TripleColoring (n + 1)} {P : SweptConfiguration n}
    {q : Point 2} (data : RightExtensionData χ P q) (i : Fin n) :
    data.toSweptConfiguration.point i.castSucc = P.point i := by
  simp [RightExtensionData.toSweptConfiguration]

@[simp] theorem RightExtensionData.toSweptConfiguration_point_last
    {n : ℕ} {χ : TripleColoring (n + 1)} {P : SweptConfiguration n}
    {q : Point 2} (data : RightExtensionData χ P q) :
    data.toSweptConfiguration.point (Fin.last n) = q := by
  simp [RightExtensionData.toSweptConfiguration]

/-- A coloring on `n + 1` vertices is determined by its initial restriction
and all triples containing its last vertex. -/
theorem TripleColoring.ext_succ {n : ℕ} {χ ψ : TripleColoring (n + 1)}
    (hinitial : χ.restrict (finInitialOrderEmbedding n) =
      ψ.restrict (finInitialOrderEmbedding n))
    (hlast : ∀ i j (hij : i < j),
      χ.lastPairColor i j hij = ψ.lastPairColor i j hij) :
    χ = ψ := by
  funext t
  rcases t with ⟨i, j, k, hij, hjk⟩
  by_cases hk : k = Fin.last n
  · subst k
    have hiLast : i ≠ Fin.last n := ne_of_lt (hij.trans hjk)
    have hjLast : j ≠ Fin.last n := ne_of_lt hjk
    obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hiLast
    obtain ⟨j', rfl⟩ := Fin.eq_castSucc_of_ne_last hjLast
    have hij' : i' < j' := Fin.castSucc_lt_castSucc_iff.mp hij
    simpa [TripleColoring.lastPairColor] using hlast i' j' hij'
  · have hkLast : k < Fin.last n := Fin.lt_last_iff_ne_last.mpr hk
    have hjLast : j ≠ Fin.last n := ne_of_lt (hjk.trans hkLast)
    have hiLast : i ≠ Fin.last n := ne_of_lt (hij.trans (hjk.trans hkLast))
    obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hiLast
    obtain ⟨j', rfl⟩ := Fin.eq_castSucc_of_ne_last hjLast
    obtain ⟨k', rfl⟩ := Fin.eq_castSucc_of_ne_last hk
    have hij' : i' < j' := Fin.castSucc_lt_castSucc_iff.mp hij
    have hjk' : j' < k' := Fin.castSucc_lt_castSucc_iff.mp hjk
    have h := congrFun hinitial ⟨i', j', k', hij', hjk'⟩
    simpa [TripleColoring.restrict, OrderedTriple.map,
      finInitialOrderEmbedding] using h

/-- Exact realization-sensitive recurrence for adjoining the rightmost point.
The existential parent configuration is retained rather than quotiented by its
triple coloring. -/
theorem isSweepRealizable_succ_iff_exists_rightExtensionData {n : ℕ}
    (χ : TripleColoring (n + 1)) :
    IsSweepRealizable χ ↔
      ∃ (P : SweptConfiguration n) (q : Point 2),
        RightExtensionData χ P q := by
  constructor
  · rintro ⟨Q, hQ⟩
    let P := Q.restrict (finInitialOrderEmbedding n)
    let q := Q.point (Fin.last n)
    refine ⟨P, q, ?_⟩
    refine {
      right := ?_
      generalPosition := ?_
      initialColoring := ?_
      lastPairColor := ?_
    }
    · intro i
      exact Q.sweep_strictMono (Fin.castSucc_lt_last i)
    · intro i j hij
      apply Q.generalPosition
      · intro h
        exact hij ((Fin.castSucc_injective n) h)
      · exact Fin.castSucc_ne_last i
      · exact Fin.castSucc_ne_last j
    · rw [Q.restrict_tripleColoring, hQ]
    · intro i j hij
      have h := congrFun hQ
        ⟨i.castSucc, j.castSucc, Fin.last n,
          Fin.castSucc_lt_castSucc_iff.mpr hij, Fin.castSucc_lt_last j⟩
      simpa [P, q, SweptConfiguration.tripleColoring,
        SweptConfiguration.turn, TripleColoring.lastPairColor] using h
  · rintro ⟨P, q, data⟩
    refine ⟨data.toSweptConfiguration, ?_⟩
    apply TripleColoring.ext_succ
    · calc
        data.toSweptConfiguration.tripleColoring.restrict
            (finInitialOrderEmbedding n) = P.tripleColoring := by
              funext t
              simp [RightExtensionData.toSweptConfiguration,
                SweptConfiguration.tripleColoring, SweptConfiguration.turn,
                TripleColoring.restrict, OrderedTriple.map,
                finInitialOrderEmbedding]
        _ = χ.restrict (finInitialOrderEmbedding n) := data.initialColoring
    · intro i j hij
      simpa [TripleColoring.lastPairColor,
        SweptConfiguration.tripleColoring, SweptConfiguration.turn] using
        data.lastPairColor i j hij

end

end ErdosSzekeres

end
