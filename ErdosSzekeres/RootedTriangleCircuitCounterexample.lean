module

public import ErdosSzekeres.Convexity

@[expose] public section

/-!
# A sharp obstruction to two-anchor rooted-triangle elimination

Ordinary planar circuit elimination can preserve one selected support point,
but it cannot in general preserve two.  This exact rational configuration
certifies the failure while retaining general position and two nested rooted
triangles.
-/

namespace ErdosSzekeres
namespace RootedTriangleCircuitCounterexample

noncomputable section

def RootedTriangle (r a b c : Point 2) : Prop :=
  InsideTriangleBySigns a b c r

def a : Point 2 := ![0, 1]
def b : Point 2 := ![-1, 0]
def c : Point 2 := ![1, 0]
def d : Point 2 := ![-10, 4]
def e : Point 2 := ![10, 5]
def f : Point 2 := ![1, -4]
def p : Point 2 := ![(1 : ℝ) / 10, (4 : ℝ) / 5]

def support : Finset (Point 2) := {p, a, b, c, d, e, f}

theorem p_rooted_in_abc : RootedTriangle p a b c := by
  norm_num [RootedTriangle, InsideTriangleBySigns, orientation, p, a, b, c]

theorem a_rooted_in_def : RootedTriangle a d e f := by
  norm_num [RootedTriangle, InsideTriangleBySigns, orientation, a, d, e, f]

set_option maxRecDepth 10000 in
theorem support_generalPosition : InGeneralPosition support := by
  intro x hx y hy z hz hxy hxz hyz
  simp only [support, Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [orientation, p, a, b, c, d, e, f] at *

/-- Even with seven points in general position and two nested rooted
triangles sharing only the eliminated point `a`, no replacement from the
second triangle preserves both anchors `b` and `c`. -/
theorem no_two_anchor_replacement :
    ¬∃ x ∈ ({d, e, f} : Finset (Point 2)), RootedTriangle p b c x := by
  rintro ⟨x, hx, hroot⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;>
    norm_num [RootedTriangle, InsideTriangleBySigns, orientation,
      p, b, c, d, e, f] at hroot

/-- Kernel-checked package refuting the natural two-anchor strong-elimination
contract. -/
theorem two_anchor_strong_elimination_counterexample :
    InGeneralPosition support ∧ RootedTriangle p a b c ∧
      RootedTriangle a d e f ∧
        ¬∃ x ∈ ({d, e, f} : Finset (Point 2)), RootedTriangle p b c x :=
  ⟨support_generalPosition, p_rooted_in_abc, a_rooted_in_def,
    no_two_anchor_replacement⟩

end

end RootedTriangleCircuitCounterexample
end ErdosSzekeres

end
