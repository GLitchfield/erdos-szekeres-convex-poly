module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticAtoms

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Alternate-depth-two semantic helpers, segment 007. -/

theorem fin11AltDepth2_capSet_iff_mask0087 (chi : TripleColoring 11) :
    IsCapSet chi {0, 1, 2, 4, 6} ↔
      chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem fin11AltDepth2_capSet_iff_mask0327 (chi : TripleColoring 11) :
    IsCapSet chi {0, 1, 2, 6, 8} ↔
      chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem fin11AltDepth2_capSet_iff_mask0563 (chi : TripleColoring 11) :
    IsCapSet chi {0, 1, 4, 5, 9} ↔
      chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem fin11AltDepth2_capSet_iff_mask0782 (chi : TripleColoring 11) :
    IsCapSet chi {1, 2, 3, 8, 9} ↔
      chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem fin11AltDepth2_capSet_iff_mask1171 (chi : TripleColoring 11) :
    IsCapSet chi {0, 1, 4, 7, 10} ↔
      chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem fin11AltDepth2_capSet_iff_mask1336 (chi : TripleColoring 11) :
    IsCapSet chi {3, 4, 5, 8, 10} ↔
      chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem fin11AltDepth2_capSet_iff_mask1618 (chi : TripleColoring 11) :
    IsCapSet chi {1, 4, 6, 9, 10} ↔
      chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem fin11AltDepth2_cupSet_iff_mask0185 (chi : TripleColoring 11) :
    IsCupSet chi {0, 3, 4, 5, 7} ↔
      chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem fin11AltDepth2_cupSet_iff_mask0406 (chi : TripleColoring 11) :
    IsCupSet chi {1, 2, 4, 7, 8} ↔
      chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem fin11AltDepth2_cupSet_iff_mask0647 (chi : TripleColoring 11) :
    IsCupSet chi {0, 1, 2, 7, 9} ↔
      chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem fin11AltDepth2_cupSet_iff_mask0856 (chi : TripleColoring 11) :
    IsCupSet chi {3, 4, 6, 8, 9} ↔
      chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem fin11AltDepth2_cupSet_iff_mask1078 (chi : TripleColoring 11) :
    IsCupSet chi {1, 2, 4, 5, 10} ↔
      chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem fin11AltDepth2_cupSet_iff_mask1190 (chi : TripleColoring 11) :
    IsCupSet chi {1, 2, 5, 7, 10} ↔
      chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem fin11AltDepth2_cupSet_iff_mask1425 (chi : TripleColoring 11) :
    IsCupSet chi {0, 4, 7, 8, 10} ↔
      chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem fin11AltDepth2_cupSet_iff_mask1712 (chi : TripleColoring 11) :
    IsCupSet chi {4, 5, 7, 9, 10} ↔
      chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem fin11AltDepth2_fiveSubset_mask0315 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 1, 3, 4, 5, 8} →
      polygon.card = 5 →
        polygon = {0, 1, 3, 4, 5} ∨
          polygon = {0, 1, 3, 4, 8} ∨
          polygon = {0, 1, 3, 5, 8} ∨
          polygon = {0, 1, 4, 5, 8} ∨
          polygon = {0, 3, 4, 5, 8} ∨
          polygon = {1, 3, 4, 5, 8} := by decide

theorem fin11AltDepth2_fiveSubset_mask0615 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 1, 2, 5, 6, 9} →
      polygon.card = 5 →
        polygon = {0, 1, 2, 5, 6} ∨
          polygon = {0, 1, 2, 5, 9} ∨
          polygon = {0, 1, 2, 6, 9} ∨
          polygon = {0, 1, 5, 6, 9} ∨
          polygon = {0, 2, 5, 6, 9} ∨
          polygon = {1, 2, 5, 6, 9} := by decide

theorem fin11AltDepth2_fiveSubset_mask0851 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 1, 4, 6, 8, 9} →
      polygon.card = 5 →
        polygon = {0, 1, 4, 6, 8} ∨
          polygon = {0, 1, 4, 6, 9} ∨
          polygon = {0, 1, 4, 8, 9} ∨
          polygon = {0, 1, 6, 8, 9} ∨
          polygon = {0, 4, 6, 8, 9} ∨
          polygon = {1, 4, 6, 8, 9} := by decide

theorem fin11AltDepth2_fiveSubset_mask1396 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {2, 4, 5, 6, 8, 10} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 8} ∨
          polygon = {2, 4, 5, 6, 10} ∨
          polygon = {2, 4, 5, 8, 10} ∨
          polygon = {2, 4, 6, 8, 10} ∨
          polygon = {2, 5, 6, 8, 10} ∨
          polygon = {4, 5, 6, 8, 10} := by decide

theorem fin11AltDepth2_fiveSubset_mask1638 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {1, 2, 5, 6, 9, 10} →
      polygon.card = 5 →
        polygon = {1, 2, 5, 6, 9} ∨
          polygon = {1, 2, 5, 6, 10} ∨
          polygon = {1, 2, 5, 9, 10} ∨
          polygon = {1, 2, 6, 9, 10} ∨
          polygon = {1, 5, 6, 9, 10} ∨
          polygon = {2, 5, 6, 9, 10} := by decide

theorem fin11AltDepth2_fiveSubset_mask1861 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 2, 6, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 6, 8, 9} ∨
          polygon = {0, 2, 6, 8, 10} ∨
          polygon = {0, 2, 6, 9, 10} ∨
          polygon = {0, 2, 8, 9, 10} ∨
          polygon = {0, 6, 8, 9, 10} ∨
          polygon = {2, 6, 8, 9, 10} := by decide

theorem fin11AltDepth2_strongSet_iff_mask0410 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {1, 3, 4, 7, 8} ↔
      Fin11AltDepth2StrongQuad chi 1 3 4 7
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 1 3 4 8
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 1 3 7 8
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 1 4 7 8
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 3 4 7 8
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 1) (j := 3) (k := 4) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 1) (j := 3) (k := 4) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 1) (j := 3) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 1) (j := 4) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 3) (j := 4) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin11AltDepth2StrongQuad]

theorem fin11AltDepth2_strongSet_iff_mask0653 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 2, 3, 7, 9} ↔
      Fin11AltDepth2StrongQuad chi 0 2 3 7
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 0 2 3 9
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 0 2 7 9
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 0 3 7 9
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 2 3 7 9
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 0) (j := 2) (k := 3) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 0) (j := 2) (k := 3) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 0) (j := 2) (k := 7) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 0) (j := 3) (k := 7) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 2) (j := 3) (k := 7) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin11AltDepth2StrongQuad]

theorem fin11AltDepth2_strongSet_iff_mask0866 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {1, 5, 6, 8, 9} ↔
      Fin11AltDepth2StrongQuad chi 1 5 6 8
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 1 5 6 9
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 1 5 8 9
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 1 6 8 9
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 5 6 8 9
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 1) (j := 5) (k := 6) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 1) (j := 5) (k := 6) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 1) (j := 5) (k := 8) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 1) (j := 6) (k := 8) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 5) (j := 6) (k := 8) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin11AltDepth2StrongQuad]

theorem fin11AltDepth2_strongSet_iff_mask1069 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 2, 3, 5, 10} ↔
      Fin11AltDepth2StrongQuad chi 0 2 3 5
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 0 2 3 10
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 0 2 5 10
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 0 3 5 10
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 2 3 5 10
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 0) (j := 2) (k := 3) (l := 5)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 0) (j := 2) (k := 3) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 0) (j := 2) (k := 5) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 0) (j := 3) (k := 5) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 2) (j := 3) (k := 5) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin11AltDepth2StrongQuad]

theorem fin11AltDepth2_strongSet_iff_mask1291 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 1, 3, 8, 10} ↔
      Fin11AltDepth2StrongQuad chi 0 1 3 8
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 0 1 3 10
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 0 1 8 10
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 0 3 8 10
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 1 3 8 10
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 0) (j := 1) (k := 3) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 0) (j := 1) (k := 3) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 0) (j := 1) (k := 8) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 0) (j := 3) (k := 8) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 1) (j := 3) (k := 8) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin11AltDepth2StrongQuad]

theorem fin11AltDepth2_strongSet_iff_mask1564 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {2, 3, 4, 9, 10} ↔
      Fin11AltDepth2StrongQuad chi 2 3 4 9
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 2 3 4 10
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 2 3 9 10
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 2 4 9 10
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 3 4 9 10
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 2) (j := 3) (k := 4) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 2) (j := 3) (k := 4) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 2) (j := 3) (k := 9) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 2) (j := 4) (k := 9) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 3) (j := 4) (k := 9) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin11AltDepth2StrongQuad]

theorem fin11AltDepth2_strongSet_iff_mask1860 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {2, 6, 8, 9, 10} ↔
      Fin11AltDepth2StrongQuad chi 2 6 8 9
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 2 6 8 10
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 2 6 9 10
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 2 8 9 10
        (by decide) (by decide) (by decide) ∧
      Fin11AltDepth2StrongQuad chi 6 8 9 10
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 2) (j := 6) (k := 8) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 2) (j := 6) (k := 8) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 2) (j := 6) (k := 9) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 2) (j := 8) (k := 9) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [Fin11AltDepth2StrongQuad] using h
          (i := 6) (j := 8) (k := 9) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin11AltDepth2StrongQuad]

end ErdosSzekeres

end
