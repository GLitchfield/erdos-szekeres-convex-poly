module

public import ErdosSzekeres.Duality
public import ErdosSzekeres.SynchronizedFiveFanFin11BranchInterface

@[expose] public section

namespace ErdosSzekeres

/-!
# Color duality for the Fin11 two-bit interface

The results in this module are certificate-free.  They complement every turn,
swap the two semantic fan alternatives, and transport a producer from the
complementary two-bit branch.
-/

/-- Pointwise color complementation is an involution on triple colorings. -/
@[simp] theorem TripleColoring.dual_dual {n : ℕ}
    (chi : TripleColoring n) : chi.dual.dual = chi := by
  funext t
  exact Turn.dual_dual (chi t)

private theorem turnSequenceAllowed_dual_iff (a b c d : Turn) :
    TurnSequenceAllowed
        (Turn.dual a) (Turn.dual b) (Turn.dual c) (Turn.dual d) ↔
      TurnSequenceAllowed a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [TurnSequenceAllowed, Turn.dual]

/-- The one-change law is invariant under complementing every turn. -/
theorem oneChangeOn_dual_iff {n : ℕ}
    (chi : TripleColoring n) (s : Finset (Fin n)) :
    OneChangeOn chi.dual s ↔ OneChangeOn chi s := by
  simp only [OneChangeOn, TripleColoring.dual_apply,
    turnSequenceAllowed_dual_iff]

/-- Complementing a coloring complements both frozen branch colors. -/
theorem synchronizedFiveFanFin11TwoBitBranch_dual_iff
    (first second : Turn) (chi : TripleColoring 11) :
    SynchronizedFiveFanFin11TwoBitBranch first second chi.dual ↔
      SynchronizedFiveFanFin11TwoBitBranch
        (Turn.dual first) (Turn.dual second) chi := by
  constructor
  · rintro ⟨hfirst, hsecond⟩
    constructor
    · have h := congrArg Turn.dual hfirst
      simpa only [TripleColoring.dual_apply, Turn.dual_dual] using h
    · have h := congrArg Turn.dual hsecond
      simpa only [TripleColoring.dual_apply, Turn.dual_dual] using h
  · rintro ⟨hfirst, hsecond⟩
    constructor
    · rw [TripleColoring.dual_apply, hfirst, Turn.dual_dual]
    · rw [TripleColoring.dual_apply, hsecond, Turn.dual_dual]

private theorem synchronizedFiveFanFin11Conclusion_dual
    (chi : TripleColoring 11)
    (h : SynchronizedFiveFanFin11Conclusion chi) :
    SynchronizedFiveFanFin11Conclusion chi.dual := by
  rcases h with ⟨side, pivot, hpivot, hcard, hlower | hupper⟩
  · refine ⟨side, pivot, hpivot, hcard, Or.inr ⟨hlower.1.dual, ?_⟩⟩
    intro polygon hsubset hpolygonCard hstrong
    exact isCapSet_dual_iff.mpr
      (hlower.2 polygon hsubset hpolygonCard
        (isStrongPolygonSet_dual_iff.mp hstrong))
  · refine ⟨side, pivot, hpivot, hcard, Or.inl ⟨hupper.1.dual, ?_⟩⟩
    intro polygon hsubset hpolygonCard hstrong
    exact isCupSet_dual_iff.mpr
      (hupper.2 polygon hsubset hpolygonCard
        (isStrongPolygonSet_dual_iff.mp hstrong))

/-- The synchronized Fin11 semantic conclusion is invariant under duality. -/
theorem synchronizedFiveFanFin11Conclusion_dual_iff
    (chi : TripleColoring 11) :
    SynchronizedFiveFanFin11Conclusion chi.dual ↔
      SynchronizedFiveFanFin11Conclusion chi := by
  constructor
  · intro h
    have hdual := synchronizedFiveFanFin11Conclusion_dual chi.dual h
    simpa only [TripleColoring.dual_dual] using hdual
  · exact synchronizedFiveFanFin11Conclusion_dual chi

/-- A producer for the complementary two-bit branch yields the original one. -/
theorem synchronizedFiveFanFin11BranchForces_dual
    {first second : Turn} :
    SynchronizedFiveFanFin11BranchForces
        (Turn.dual first) (Turn.dual second) →
      SynchronizedFiveFanFin11BranchForces first second := by
  intro hcomplement chi hone hnoStrong hbranch
  have honeDual : OneChangeOn chi.dual Finset.univ :=
    (oneChangeOn_dual_iff chi Finset.univ).2 hone
  have hnoStrongDual :
      ¬ ContainsStrongPolygonSet chi.dual Finset.univ 6 := by
    intro hstrongDual
    exact hnoStrong (containsStrongPolygonSet_dual_iff.mp hstrongDual)
  have hbranchDual :
      SynchronizedFiveFanFin11TwoBitBranch
        (Turn.dual first) (Turn.dual second) chi.dual := by
    apply (synchronizedFiveFanFin11TwoBitBranch_dual_iff
      (Turn.dual first) (Turn.dual second) chi).2
    simpa only [Turn.dual_dual] using hbranch
  have hconclusionDual :=
    hcomplement chi.dual honeDual hnoStrongDual hbranchDual
  exact (synchronizedFiveFanFin11Conclusion_dual_iff chi).mp
    hconclusionDual

end ErdosSzekeres

end
