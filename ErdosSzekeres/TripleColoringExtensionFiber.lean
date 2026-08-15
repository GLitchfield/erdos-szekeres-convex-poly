module

public import ErdosSzekeres.TripleColoringGeometricExtension

@[expose] public section

/-!
# Rightmost-extension fibers of ordered triple colorings

This file separates abstract one-change compatibility from geometric extension
of a fixed realization and from extension over all realizations of a parent
coloring.  It also records the colors involving the new last vertex as a link
on the increasing pairs of the parent.
-/

namespace ErdosSzekeres

noncomputable section

/-- An increasing pair of indices. -/
structure OrderedPair (n : ℕ) where
  i : Fin n
  j : Fin n
  hij : i < j

/-- The colors of all triples formed by an old pair and a new last vertex. -/
abbrev RightExtensionLink (n : ℕ) := OrderedPair n → Turn

namespace TripleColoring

/-- Forget a child coloring except for the colors of triples containing its
last vertex. -/
def rightExtensionLink {n : ℕ} (ψ : TripleColoring (n + 1)) : RightExtensionLink n :=
  fun p ↦ ψ.lastPairColor p.i p.j p.hij

/-- The parent restriction and right-extension link carried by a child
coloring. -/
def rightExtensionSignature {n : ℕ} (ψ : TripleColoring (n + 1)) :
    TripleColoring n × RightExtensionLink n :=
  (ψ.restrict (finInitialOrderEmbedding n), ψ.rightExtensionLink)

/-- A child coloring is determined by its parent restriction and its
right-extension link. -/
theorem ext_succ_of_rightExtensionLink_eq {n : ℕ}
    {χ ψ : TripleColoring (n + 1)}
    (hinitial : χ.restrict (finInitialOrderEmbedding n) =
      ψ.restrict (finInitialOrderEmbedding n))
    (hlink : χ.rightExtensionLink = ψ.rightExtensionLink) : χ = ψ := by
  apply TripleColoring.ext_succ hinitial
  intro i j hij
  exact congrFun hlink ⟨i, j, hij⟩

/-- Recording the parent restriction and right-extension link loses no child
coloring information. -/
theorem rightExtensionSignature_injective {n : ℕ} :
    Function.Injective
      (rightExtensionSignature : TripleColoring (n + 1) →
        TripleColoring n × RightExtensionLink n) := by
  intro χ ψ h
  apply ext_succ_of_rightExtensionLink_eq
  · simpa [rightExtensionSignature] using congrArg Prod.fst h
  · simpa [rightExtensionSignature] using congrArg Prod.snd h

end TripleColoring

/-- Pair links satisfying every new one-change constraint over a fixed parent
coloring. -/
def AbstractRightExtensionLinkFiber {n : ℕ} (χ : TripleColoring n) :
    Set (RightExtensionLink n) :=
  {link | ∀ {i j k : Fin n}, (hij : i < j) → (hjk : j < k) →
    TurnSequenceAllowed
      (χ ⟨i, j, k, hij, hjk⟩)
      (link ⟨i, j, hij⟩)
      (link ⟨i, k, hij.trans hjk⟩)
      (link ⟨j, k, hjk⟩)}

/-- `LastExtensionCompatible` is exactly membership of the child's link in
the abstract link fiber over its own parent restriction. -/
@[simp] theorem rightExtensionLink_mem_abstractRightExtensionLinkFiber_iff
    {n : ℕ} (ψ : TripleColoring (n + 1)) :
    ψ.rightExtensionLink ∈ AbstractRightExtensionLinkFiber
        (ψ.restrict (finInitialOrderEmbedding n)) ↔
      LastExtensionCompatible ψ := by
  rfl

/-- Abstract child colorings extending a fixed parent and satisfying all new
one-change constraints. -/
def AbstractRightExtensionFiber {n : ℕ} (χ : TripleColoring n) :
    Set (TripleColoring (n + 1)) :=
  {ψ | ψ.restrict (finInitialOrderEmbedding n) = χ ∧
    LastExtensionCompatible ψ}

@[simp] theorem mem_abstractRightExtensionFiber_iff {n : ℕ}
    (χ : TripleColoring n) (ψ : TripleColoring (n + 1)) :
    ψ ∈ AbstractRightExtensionFiber χ ↔
      ψ.restrict (finInitialOrderEmbedding n) = χ ∧
        LastExtensionCompatible ψ := by
  rfl

/-- Abstract child membership can equivalently be stated using the pair-link
fiber. -/
theorem mem_abstractRightExtensionFiber_iff_link {n : ℕ}
    (χ : TripleColoring n) (ψ : TripleColoring (n + 1)) :
    ψ ∈ AbstractRightExtensionFiber χ ↔
      ψ.restrict (finInitialOrderEmbedding n) = χ ∧
        ψ.rightExtensionLink ∈ AbstractRightExtensionLinkFiber χ := by
  constructor
  · rintro ⟨hparent, hcompatible⟩
    refine ⟨hparent, ?_⟩
    rw [← hparent]
    exact (rightExtensionLink_mem_abstractRightExtensionLinkFiber_iff ψ).mpr hcompatible
  · rintro ⟨hparent, hlink⟩
    refine ⟨hparent, ?_⟩
    rw [← hparent] at hlink
    exact (rightExtensionLink_mem_abstractRightExtensionLinkFiber_iff ψ).mp hlink

/-- Geometric child colorings obtainable by adding one point to a particular
swept parent configuration. -/
def FixedGeometricRightExtensionFiber {n : ℕ} (P : SweptConfiguration n) :
    Set (TripleColoring (n + 1)) :=
  {ψ | ∃ q : Point 2, RightExtensionData ψ P q}

@[simp] theorem mem_fixedGeometricRightExtensionFiber_iff {n : ℕ}
    (P : SweptConfiguration n) (ψ : TripleColoring (n + 1)) :
    ψ ∈ FixedGeometricRightExtensionFiber P ↔
      ∃ q : Point 2, RightExtensionData ψ P q := by
  rfl

/-- Every geometric extension of a fixed realization is an abstract compatible
extension of the coloring induced by that same realization. -/
theorem mem_abstractRightExtensionFiber_of_mem_fixedGeometricRightExtensionFiber
    {n : ℕ} {P : SweptConfiguration n} {ψ : TripleColoring (n + 1)}
    (hψ : ψ ∈ FixedGeometricRightExtensionFiber P) :
    ψ ∈ AbstractRightExtensionFiber P.tripleColoring := by
  rcases hψ with ⟨q, data⟩
  refine ⟨data.initialColoring.symm, ?_⟩
  have hrealizable : IsSweepRealizable ψ :=
    (isSweepRealizable_succ_iff_exists_rightExtensionData ψ).2 ⟨P, q, data⟩
  have honeChange : OneChangeOn ψ Finset.univ := by
    rcases hrealizable with ⟨Q, rfl⟩
    intro i j k l hij hjk hkl _ _ _ _
    exact Q.turnSequenceAllowed i j k l hij hjk hkl
  intro i j k hij hjk
  exact ((oneChangeOn_univ_succ_iff (n := n) ψ).mp honeChange).2
    (i := i) (j := j) (k := k) hij hjk

/-- Geometric extensions over all swept realizations of a parent coloring.
The realizing parent configuration remains an explicit membership witness. -/
def GeometricRightExtensionFiber {n : ℕ} (χ : TripleColoring n) :
    Set (TripleColoring (n + 1)) :=
  {ψ | ∃ P : SweptConfiguration n,
    P.tripleColoring = χ ∧ ψ ∈ FixedGeometricRightExtensionFiber P}

/-- A child belongs to the union-over-realizations geometric fiber exactly
when it is realizable and has the prescribed parent restriction. -/
@[simp] theorem mem_geometricRightExtensionFiber_iff {n : ℕ}
    (χ : TripleColoring n) (ψ : TripleColoring (n + 1)) :
    ψ ∈ GeometricRightExtensionFiber χ ↔
      IsSweepRealizable ψ ∧
        ψ.restrict (finInitialOrderEmbedding n) = χ := by
  constructor
  · rintro ⟨P, hparent, q, data⟩
    constructor
    · exact (isSweepRealizable_succ_iff_exists_rightExtensionData ψ).2
        ⟨P, q, data⟩
    · exact data.initialColoring.symm.trans hparent
  · rintro ⟨hrealizable, hparent⟩
    rcases (isSweepRealizable_succ_iff_exists_rightExtensionData ψ).1 hrealizable with
      ⟨P, q, data⟩
    exact ⟨P, data.initialColoring.trans hparent, q, data⟩

/-- Filter any child-coloring fiber by an additional predicate. -/
def PredicateFilteredRightExtensionFiber {n : ℕ}
    (fiber : Set (TripleColoring (n + 1)))
    (predicate : TripleColoring (n + 1) → Prop) :
    Set (TripleColoring (n + 1)) :=
  {ψ | ψ ∈ fiber ∧ predicate ψ}

@[simp] theorem mem_predicateFilteredRightExtensionFiber_iff {n : ℕ}
    (fiber : Set (TripleColoring (n + 1)))
    (predicate : TripleColoring (n + 1) → Prop)
    (ψ : TripleColoring (n + 1)) :
    ψ ∈ PredicateFilteredRightExtensionFiber fiber predicate ↔
      ψ ∈ fiber ∧ predicate ψ := by
  rfl

end

end ErdosSzekeres

end
