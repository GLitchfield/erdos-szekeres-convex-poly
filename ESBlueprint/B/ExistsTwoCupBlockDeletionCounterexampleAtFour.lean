import ErdosSzekeres.StructuralChargingCore
import ErdosSzekeres.RankProfileCollision

namespace ErdosSzekeres

/-- Explicit six-point3|3 cup-block counterexample to lowering Claim D growth to strong size four: OneChange, no four-cap and no strong five-set, while the strong four-set{0,2,3,5} avoids canonical deletion{1,4}. Its cup portion has three points and apex2. This certifies the documented induction threshold obstruction using finite kernel checking.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.RankProfileCollision.strongPolygonSetBool_eq_true_iff
@dangling-ok Approved R20 verification of the hand proof39-41 size-four exception and why the uniform induction uses a separate base at five. This is not a refutation of the proved diagonal theorem. -/
theorem existsTwoCupBlockDeletionCounterexampleAtFour : ∃ χ : TripleColoring 6,
      IsCupSet χ ({0, 1, 2} : Finset (Fin 6)) ∧
      IsCupSet χ ({3, 4, 5} : Finset (Fin 6)) ∧
      OneChangeOn χ Finset.univ ∧
      (¬ContainsCapSet χ Finset.univ 4) ∧
      (¬ContainsStrongPolygonSet χ Finset.univ 5) ∧
      IsStrongPolygonSet χ ({0, 2, 3, 5} : Finset (Fin 6)) ∧
      ({0, 2, 3, 5} : Finset (Fin 6)).card = 4 ∧
      Disjoint ({0, 2, 3, 5} : Finset (Fin 6)) {1, 4} := by
  let rightCodes : Finset ℕ := {14, 23, 24, 25, 34, 123, 124, 125, 134, 135}
  let χ : TripleColoring 6 := fun t ↦
    if 100 * t.i.val + 10 * t.j.val + t.k.val ∈ rightCodes then .right else .left
  let turnCheck (color : Turn) (s : Finset (Fin 6)) : Bool :=
    (List.finRange 6).all fun i ↦
      (List.finRange 6).all fun j ↦
        (List.finRange 6).all fun k ↦
          if hij : i < j then
            if hjk : j < k then
              if i ∈ s ∧ j ∈ s ∧ k ∈ s then
                decide (χ ⟨i, j, k, hij, hjk⟩ = color)
              else true
            else true
          else true
  have hTurn (color : Turn) (s : Finset (Fin 6)) :
      turnCheck color s = true ↔
        ∀ t : OrderedTriple 6, t.i ∈ s → t.j ∈ s → t.k ∈ s → χ t = color := by
    constructor
    · intro h t hi hj hk
      rcases t with ⟨i, j, k, hij, hjk⟩
      have hiCheck := (List.all_eq_true.mp h) i (List.mem_finRange i)
      have hjCheck := (List.all_eq_true.mp hiCheck) j (List.mem_finRange j)
      have hkCheck := (List.all_eq_true.mp hjCheck) k (List.mem_finRange k)
      simpa [turnCheck, hij, hjk, hi, hj, hk] using hkCheck
    · intro h
      apply List.all_eq_true.mpr
      intro i _
      apply List.all_eq_true.mpr
      intro j _
      apply List.all_eq_true.mpr
      intro k _
      by_cases hij : i < j
      · by_cases hjk : j < k
        · by_cases hm : i ∈ s ∧ j ∈ s ∧ k ∈ s
          · simp [hij, hjk, hm, h ⟨i, j, k, hij, hjk⟩ hm.1 hm.2.1 hm.2.2]
          · simp [hij, hjk, hm]
        · simp [hij, hjk]
      · simp [hij]
  letI : ∀ a b c d : Turn, Decidable (TurnSequenceAllowed a b c d) :=
    fun a b c d ↦ by
      unfold TurnSequenceAllowed
      infer_instance
  let oneChangeCheck : Bool :=
    (List.finRange 6).all fun i ↦
      (List.finRange 6).all fun j ↦
        (List.finRange 6).all fun k ↦
          (List.finRange 6).all fun l ↦
            if hij : i < j then
              if hjk : j < k then
                if hkl : k < l then
                  decide (TurnSequenceAllowed
                    (χ ⟨i, j, k, hij, hjk⟩)
                    (χ ⟨i, j, l, hij, hjk.trans hkl⟩)
                    (χ ⟨i, k, l, hij.trans hjk, hkl⟩)
                    (χ ⟨j, k, l, hjk, hkl⟩))
                else true
              else true
            else true
  have hOneCheck : oneChangeCheck = true := by decide
  have hOne : OneChangeOn χ Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    have hiCheck := (List.all_eq_true.mp hOneCheck) i (List.mem_finRange i)
    have hjCheck := (List.all_eq_true.mp hiCheck) j (List.mem_finRange j)
    have hkCheck := (List.all_eq_true.mp hjCheck) k (List.mem_finRange k)
    have hlCheck := (List.all_eq_true.mp hkCheck) l (List.mem_finRange l)
    simpa [oneChangeCheck, hij, hjk, hkl] using hlCheck
  have hNoCapCheck : ∀ s ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
      turnCheck .right s = false := by decide
  have hNoCap : ¬ContainsCapSet χ Finset.univ 4 := by
    rintro ⟨s, hs, hcard, hcap⟩
    have hmem := Finset.mem_powersetCard.mpr ⟨hs, hcard⟩
    have hfalse := hNoCapCheck s hmem
    have htrue := (hTurn .right s).mpr hcap
    exact Bool.noConfusion (hfalse.symm.trans htrue)
  have hNoStrongCheck : ∀ s ∈ (Finset.univ : Finset (Fin 6)).powersetCard 5,
      RankProfileCollision.strongPolygonSetBool χ s = false := by decide
  have hNoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 5 := by
    rintro ⟨s, hs, hcard, hstrong⟩
    have hmem := Finset.mem_powersetCard.mpr ⟨hs, hcard⟩
    have hfalse := hNoStrongCheck s hmem
    have htrue := (RankProfileCollision.strongPolygonSetBool_eq_true_iff χ s).mpr
      hstrong
    exact Bool.noConfusion (hfalse.symm.trans htrue)
  refine ⟨χ, (hTurn .left {0, 1, 2}).mp ?_, (hTurn .left {3, 4, 5}).mp ?_,
    hOne, hNoCap, hNoStrong, ?_, ?_, ?_⟩
  · decide
  · decide
  · exact (RankProfileCollision.strongPolygonSetBool_eq_true_iff χ {0, 2, 3, 5}).mp
      (by decide)
  · decide
  · decide


end ErdosSzekeres
