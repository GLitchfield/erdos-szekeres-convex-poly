module

public import ErdosSzekeres.Decomposable

@[expose] public section

/-!
# Strong polygon sets from their five-element subsets

Any four indices of a set with at least five elements lie in one of its
five-element subsets, so a set all of whose five-subsets are strong is
strong.  The generated no-strong-six clause lemmas use this in place of a
1,296-way index case split.
-/

namespace ErdosSzekeres

theorem isStrongPolygonSet_of_forall_five {n : ℕ} (χ : TripleColoring n)
    (s : Finset (Fin n)) (hcard : 5 ≤ s.card)
    (h : ∀ t ⊆ s, t.card = 5 → IsStrongPolygonSet χ t) :
    IsStrongPolygonSet χ s := by
  intro i j k l hij hjk hkl hi hj hk hl
  classical
  have hqs : ({i, j, k, l} : Finset (Fin n)) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hkl' : k ∉ ({l} : Finset (Fin n)) := by simp [ne_of_lt hkl]
  have hjkl : j ∉ ({k, l} : Finset (Fin n)) := by
    simp [ne_of_lt hjk, ne_of_lt (hjk.trans hkl)]
  have hijkl : i ∉ ({j, k, l} : Finset (Fin n)) := by
    simp [ne_of_lt hij, ne_of_lt (hij.trans hjk), ne_of_lt ((hij.trans hjk).trans hkl)]
  have hq4 : ({i, j, k, l} : Finset (Fin n)).card = 4 := by
    rw [Finset.card_insert_of_notMem hijkl, Finset.card_insert_of_notMem hjkl,
      Finset.card_insert_of_notMem hkl', Finset.card_singleton]
  obtain ⟨m, hms, hmq⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card
      (s := ({i, j, k, l} : Finset (Fin n))) (t := s) (by omega)
  have hu : insert m ({i, j, k, l} : Finset (Fin n)) ⊆ s := Finset.insert_subset hms hqs
  have hucard : (insert m ({i, j, k, l} : Finset (Fin n))).card = 5 := by
    rw [Finset.card_insert_of_notMem hmq, hq4]
  exact h _ hu hucard hij hjk hkl (by simp) (by simp) (by simp) (by simp)

end ErdosSzekeres

end
