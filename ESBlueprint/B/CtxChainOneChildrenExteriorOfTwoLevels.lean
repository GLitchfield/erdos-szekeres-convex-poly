import ESBlueprint.B.CtxNonunitChildrenExteriorOfTwoLevels
import ESBlueprint.B.CtxTwoBoundaryMarkerEraseNormalize

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Two distinct actual indexed levels on one axis put all children whose pure chosen chain extension is at most one in a common exterior region beyond every indexed chosen marker. The orientation is fixed by positions on the younger and older levels. No global parameter, k, capacity, positivity or activity hypothesis is needed. An auxiliary context with global four and a sufficiently large k permits reuse of the existing nonunit geometry without changing word or history. Supports the maximal chosen-capacity-three case at global five.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_chain_one_children_exterior_of_two_levels (σ : Ctx.Context) (s : Ctx.Side) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) :
  (x < y ∧ ∀ p ∈ σ.childPositions,
    σ.chainExt s p p ≤ 1 →
      ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z < p) ∨
  (y < x ∧ ∀ p ∈ σ.childPositions,
    σ.chainExt s p p ≤ 1 →
      ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, p < z) := by
  classical
  have hEach (p : ℕ) (hp : p ∈ σ.childPositions) (hc : σ.chainExt s p p ≤ 1) :
      (x < y ∧ ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z < p) ∨
      (y < x ∧ ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, p < z) := by
    let τ : Context := { σ with a := 4, u := 4, k := σ.joinExt s p p + 3 }
    have hCap : 2 ≤ (match s with
        | Side.lower => τ.cupLimit p p | Side.upper => τ.capLimit p p) := by
      cases s
      · change 2 ≤ min (3 - σ.chainExt Side.lower p p)
          ((σ.joinExt Side.lower p p + 3) - 1 - σ.joinExt Side.lower p p)
        omega
      · change 2 ≤ min (3 - σ.chainExt Side.upper p p)
          ((σ.joinExt Side.upper p p + 3) - 1 - σ.joinExt Side.upper p p)
        omega
    have hg : (match s with | Side.lower => τ.u | Side.upper => τ.a) ≤ 4 := by
      cases s <;> exact le_rfl
    rcases ctx_nonunit_children_exterior_of_two_levels τ s N M x y hN hM hNM hNs hMs hx hy hg with hl | hr
    · exact Or.inl ⟨hl.1, hl.2 p hp hCap⟩
    · exact Or.inr ⟨hr.1, hr.2 p hp hCap⟩
  let υ : Context := { σ with a := 4, u := 4 }
  have hg : (match s with | Side.lower => υ.u | Side.upper => υ.a) ≤ 4 := by
    cases s <;> exact le_rfl
  rcases ctx_nonunit_children_exterior_of_two_levels υ s N M x y hN hM hNM hNs hMs hx hy hg with hl | hr
  · refine Or.inl ⟨hl.1, ?_⟩
    intro p hp hc
    rcases hEach p hp hc with h | h
    · exact h.2
    · have := hl.1
      omega
  · refine Or.inr ⟨hr.1, ?_⟩
    intro p hp hc
    rcases hEach p hp hc with h | h
    · have := hr.1
      omega
    · exact h.2

end ErdosSzekeres
