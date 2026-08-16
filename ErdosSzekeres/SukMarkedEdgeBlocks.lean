module

public import ErdosSzekeres.Basic
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# Marked-edge block selection

This module isolates the finite selection step in the Pór--Valtr block-coarsening
mechanism.  It enumerates the marked cyclic edges in increasing order, so every
interval between consecutive selected indices contains its distinct left endpoint.
-/

namespace ErdosSzekeres

/-- `selected` lists retained cyclic vertices after cutting at the first
retained nonclosing edge.  Every consecutive selected-index block contains a
distinct marked source edge. -/
def SukMarkedEdgeBlockSelection
    (r : ℕ) (marked : Finset ℕ) : Prop :=
  ∃ selected : Fin r → ℕ,
    StrictMono selected ∧
    (∀ j, selected j < 2 * r) ∧
    ∀ j : Fin (r - 1),
      ∃ edge ∈ marked,
        selected ⟨j, by omega⟩ ≤ edge ∧
        edge < selected ⟨j + 1, by omega⟩

/-- Any `r` marked edges among the `2r` cyclic edges yield `r-1`
nonclosing marked blocks. -/
theorem exists_sukMarkedEdgeBlockSelection
    (r : ℕ) (marked : Finset ℕ)
    (hr : 3 ≤ r)
    (hmarked : marked ⊆ Finset.range (2 * r))
    (hcard : marked.card = r) :
    SukMarkedEdgeBlockSelection r marked := by
  let selected : Fin r ↪o ℕ := marked.orderEmbOfFin hcard
  refine ⟨selected, selected.strictMono, ?_, ?_⟩
  · intro j
    exact Finset.mem_range.mp (hmarked (marked.orderEmbOfFin_mem hcard j))
  · intro j
    let left : Fin r := ⟨j, by omega⟩
    refine ⟨selected left, marked.orderEmbOfFin_mem hcard left, le_rfl, ?_⟩
    apply selected.strictMono
    change (j : ℕ) < (j : ℕ) + 1
    omega

end ErdosSzekeres

end
