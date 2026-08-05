module

public import ErdosSzekeres.Decomposable

@[expose] public section

/-!
# Rooted chain endpoint footprints

The exact singleton transition in `Decomposable` says that an upper vertex
extends a lower cup, and dually a lower vertex extends an upper cap, precisely
at a sweep endpoint.  The unsplit endpoint predicate is a union of two rays,
not one interval.  This file makes the necessary left/right endpoint side an
explicit finite carrier and proves the two rays have the expected order
closure.
-/

namespace ErdosSzekeres

noncomputable section

open HasDeepBelowSplit

/-- Which endpoint of an ordered child chain lies next to a singleton root. -/
inductive SweepEndpointSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- The side-indexed version of the sweep-endpoint predicate. -/
def HasSweepEndpointSide {n : ℕ} (s : Finset (Fin n)) (q : Fin n) :
    SweepEndpointSide → Prop
  | .left => IsLeftSweepEndpoint s q
  | .right => IsRightSweepEndpoint s q

@[simp] theorem hasSweepEndpointSide_left {n : ℕ} (s : Finset (Fin n)) (q : Fin n) :
    HasSweepEndpointSide s q .left ↔ IsLeftSweepEndpoint s q := by
  rfl

@[simp] theorem hasSweepEndpointSide_right {n : ℕ} (s : Finset (Fin n)) (q : Fin n) :
    HasSweepEndpointSide s q .right ↔ IsRightSweepEndpoint s q := by
  rfl

/-- Forgetting the endpoint side recovers the existing two-ray predicate. -/
theorem exists_hasSweepEndpointSide_iff_isSweepEndpoint {n : ℕ}
    (s : Finset (Fin n)) (q : Fin n) :
    (∃ side, HasSweepEndpointSide s q side) ↔ IsSweepEndpoint s q := by
  constructor
  · rintro ⟨side, hside⟩
    cases side with
    | left => exact Or.inl hside
    | right => exact Or.inr hside
  · rintro (hleft | hright)
    · exact ⟨.left, hleft⟩
    · exact ⟨.right, hright⟩

/-- The left-endpoint ray is downward closed in the singleton position. -/
theorem HasSweepEndpointSide.anti_left {n : ℕ} {s : Finset (Fin n)}
    {q r : Fin n} (hr : HasSweepEndpointSide s r .left) (hqr : q ≤ r) :
    HasSweepEndpointSide s q .left := by
  intro x hx
  exact hqr.trans (hr x hx)

/-- The right-endpoint ray is upward closed in the singleton position. -/
theorem HasSweepEndpointSide.mono_right {n : ℕ} {s : Finset (Fin n)}
    {q r : Fin n} (hq : HasSweepEndpointSide s q .right) (hqr : q ≤ r) :
    HasSweepEndpointSide s r .right := by
  intro x hx
  exact (hq x hx).trans hqr

/-- For a genuine external singleton, the two endpoint-side states are disjoint. -/
theorem not_hasSweepEndpointSide_left_and_right {n : ℕ}
    {s : Finset (Fin n)} {q : Fin n} (hs : s.Nonempty) (hq : q ∉ s) :
    ¬(HasSweepEndpointSide s q .left ∧ HasSweepEndpointSide s q .right) := by
  exact not_isLeft_and_isRightSweepEndpoint hs hq

/-- Exact side-indexed form of the upper-singleton/lower-cup transition. -/
theorem insert_upper_isCupSet_iff_exists_endpointSide {n : ℕ}
    {χ : TripleColoring n} {lower upper cup : Finset (Fin n)}
    (h : HasDeepBelowSplit χ lower upper) (hcupSub : cup ⊆ lower)
    (hcup : IsCupSet χ cup) (hcupNonempty : cup.Nonempty)
    {q : Fin n} (hqUpper : q ∈ upper) :
    IsCupSet χ (insert q cup) ↔ ∃ side, HasSweepEndpointSide cup q side := by
  rw [h.insert_upper_isCupSet_iff_isSweepEndpoint
    hcupSub hcup hcupNonempty hqUpper,
    exists_hasSweepEndpointSide_iff_isSweepEndpoint]

/-- Exact side-indexed form of the lower-singleton/upper-cap transition. -/
theorem insert_lower_isCapSet_iff_exists_endpointSide {n : ℕ}
    {χ : TripleColoring n} {lower upper cap : Finset (Fin n)}
    (h : HasDeepBelowSplit χ lower upper) (hcapSub : cap ⊆ upper)
    (hcap : IsCapSet χ cap) (hcapNonempty : cap.Nonempty)
    {q : Fin n} (hqLower : q ∈ lower) :
    IsCapSet χ (insert q cap) ↔ ∃ side, HasSweepEndpointSide cap q side := by
  rw [h.insert_lower_isCapSet_iff_isSweepEndpoint
    hcapSub hcap hcapNonempty hqLower,
    exists_hasSweepEndpointSide_iff_isSweepEndpoint]

/-- Without the side label, successful singleton positions need not be order-convex. -/
theorem sweepEndpoint_two_ray_counterexample :
    let s : Finset (Fin 5) := {1, 3}
    IsSweepEndpoint s 0 ∧ ¬IsSweepEndpoint s 2 ∧ IsSweepEndpoint s 4 := by
  norm_num [IsSweepEndpoint, IsLeftSweepEndpoint, IsRightSweepEndpoint]
  omega

end

end ErdosSzekeres
