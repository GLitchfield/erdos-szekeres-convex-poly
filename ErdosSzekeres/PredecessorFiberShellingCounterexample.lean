module

public import ErdosSzekeres.RankProfileCollision

@[expose] public section

/-!
# Counterexample to symmetric predecessor-fiber shell coherence

The symmetric Boolean shelling rule assigns both endpoints of every exclusive
left/right predecessor-fiber event.  Already in a four-vertex all-right
decomposable coloring, consecutive right-rank events force one coordinate of
the middle vertex to be both absent and present.  Thus coherence itself fails,
before injectivity or Boolean-lattice capacity enters.
-/

namespace ErdosSzekeres
namespace PredecessorFiberShellingCounterexample

open RankProfile RankProfileCollision

/-- The frozen, noncircular symmetric shell-coherence specification. -/
def ShellCoherent {n clip : ℕ} (χ : TripleColoring n)
    (support : Finset (Fin n)) (label : Fin n → Finset (Fin clip)) : Prop :=
  ∀ u v (r : Fin clip), u < v →
    ((HasFinitePairRankAbove χ Turn.right support u v r.val ∧
        ¬HasFinitePairRankAbove χ Turn.left support u v r.val) →
      r ∈ label u ∧ r ∉ label v) ∧
    ((HasFinitePairRankAbove χ Turn.left support u v r.val ∧
        ¬HasFinitePairRankAbove χ Turn.right support u v r.val) →
      r ∉ label u ∧ r ∈ label v)

/-- An explicit recursively decomposable tree inducing the four-vertex
all-right coloring used by the bounded falsifier. -/
def tree : RankProfileCollision.DecompositionTree 4 :=
  .node (.node (.leaf 3) (.leaf 0)) (.node (.leaf 2) (.leaf 1))

def color : TripleColoring 4 := tree.coloring

theorem color_decomposable : IsDecomposable color := by
  have hwell : tree.WellFormed := by
    simp [tree, RankProfileCollision.DecompositionTree.WellFormed,
      RankProfileCollision.DecompositionTree.vertices]
  have h := RankProfileCollision.DecompositionTree.decomposableOn tree hwell
  have hvertices : tree.vertices = Finset.univ := by decide
  rw [hvertices] at h
  exact h

theorem color_no_strong_five :
    ¬ContainsStrongPolygonSet color Finset.univ 5 := by
  rintro ⟨polygon, hsub, hcard, _⟩
  have hle := Finset.card_le_card hsub
  simp at hle
  omega

/-- At coordinate one, `(1,2)` forces vertex two's bit to be zero while
`(2,3)` forces the same bit to be one. -/
theorem no_shell_coherent_label :
    ¬∃ label : Fin 4 → Finset (Fin 3),
      ShellCoherent color Finset.univ label := by
  rintro ⟨label, hcoherent⟩
  let r : Fin 3 := ⟨1, by decide⟩
  have h12 := (hcoherent (1 : Fin 4) (2 : Fin 4) r (by decide)).1
    ⟨by decide, by decide⟩
  have h23 := (hcoherent (2 : Fin 4) (3 : Fin 4) r (by decide)).1
    ⟨by decide, by decide⟩
  exact h12.2 h23.1

end PredecessorFiberShellingCounterexample
end ErdosSzekeres

end
