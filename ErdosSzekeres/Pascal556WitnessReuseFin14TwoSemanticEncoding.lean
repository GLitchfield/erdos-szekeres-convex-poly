-- Generated semantic vocabulary for the checked Fin14 distinct-witness core.
module

public import ErdosSzekeres.StructuralChargingResidualProbeVariableFiber

@[expose] public section

namespace ErdosSzekeres

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- The left side of the normalized cut used by the frozen Fin14 encoding. -/
def Pascal556WitnessReuseFin14CutLeft (cut : Fin 8) : Finset (Fin 14) :=
  Finset.univ.filter fun i => i.val < cut.val

/-- The right side of the normalized cut used by the frozen Fin14 encoding. -/
def Pascal556WitnessReuseFin14CutRight (cut : Fin 8) : Finset (Fin 14) :=
  Finset.univ.filter fun i => cut.val ≤ i.val

/-- A color variable in the frozen CNF: `true` means `Turn.left`. -/
def Pascal556WitnessReuseFin14ColorAtom (χ : TripleColoring 14)
    (a b c : Fin 14) (hab : a < b) (hbc : b < c) : Prop :=
  χ ⟨a, b, c, hab, hbc⟩ = Turn.left

/-- The exact four-vertex strong atom used by the frozen CNF. -/
def Pascal556WitnessReuseFin14Strong4Atom (χ : TripleColoring 14)
    (a b c d : Fin 14) (hab : a < b) (hbc : b < c) (hcd : c < d) : Prop :=
  χ ⟨a, b, c, hab, hbc⟩ = χ ⟨a, b, d, hab, hbc.trans hcd⟩ ∧
    χ ⟨a, c, d, hab.trans hbc, hcd⟩ = χ ⟨b, c, d, hbc, hcd⟩

/-- The exact five-vertex strong atom used by the frozen CNF. -/
def Pascal556WitnessReuseFin14Strong5Atom (χ : TripleColoring 14)
    (a b c d e : Fin 14) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e) : Prop :=
  Pascal556WitnessReuseFin14Strong4Atom χ a b c d hab hbc hcd ∧
    Pascal556WitnessReuseFin14Strong4Atom χ a b c e hab hbc (hcd.trans hde) ∧
    Pascal556WitnessReuseFin14Strong4Atom χ a b d e hab (hbc.trans hcd) hde ∧
    Pascal556WitnessReuseFin14Strong4Atom χ a c d e (hab.trans hbc) hcd hde ∧
    Pascal556WitnessReuseFin14Strong4Atom χ b c d e hbc hcd hde

/-- The conjunction of all fifteen four-vertex laws on six ordered labels. -/
def Pascal556WitnessReuseFin14Strong6Atom (χ : TripleColoring 14)
    (a b c d e f : Fin 14) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e) (hef : e < f) : Prop :=
  Pascal556WitnessReuseFin14Strong4Atom χ a b c d hab hbc hcd ∧
    Pascal556WitnessReuseFin14Strong4Atom χ a b c e hab hbc (hcd.trans hde) ∧
    Pascal556WitnessReuseFin14Strong4Atom χ a b c f hab hbc
      (hcd.trans (hde.trans hef)) ∧
    Pascal556WitnessReuseFin14Strong4Atom χ a b d e hab (hbc.trans hcd) hde ∧
    Pascal556WitnessReuseFin14Strong4Atom χ a b d f hab (hbc.trans hcd)
      (hde.trans hef) ∧
    Pascal556WitnessReuseFin14Strong4Atom χ a b e f hab
      (hbc.trans (hcd.trans hde)) hef ∧
    Pascal556WitnessReuseFin14Strong4Atom χ a c d e (hab.trans hbc) hcd hde ∧
    Pascal556WitnessReuseFin14Strong4Atom χ a c d f (hab.trans hbc) hcd
      (hde.trans hef) ∧
    Pascal556WitnessReuseFin14Strong4Atom χ a c e f (hab.trans hbc)
      (hcd.trans hde) hef ∧
    Pascal556WitnessReuseFin14Strong4Atom χ a d e f
      (hab.trans (hbc.trans hcd)) hde hef ∧
    Pascal556WitnessReuseFin14Strong4Atom χ b c d e hbc hcd hde ∧
    Pascal556WitnessReuseFin14Strong4Atom χ b c d f hbc hcd (hde.trans hef) ∧
    Pascal556WitnessReuseFin14Strong4Atom χ b c e f hbc (hcd.trans hde) hef ∧
    Pascal556WitnessReuseFin14Strong4Atom χ b d e f (hbc.trans hcd) hde hef ∧
    Pascal556WitnessReuseFin14Strong4Atom χ c d e f hcd hde hef

/-- The frozen fifteen-atom conjunction is the mathematical strong-six law. -/
theorem pascal556WitnessReuseFin14_isStrongPolygonSet_six_of_atom
    (χ : TripleColoring 14) (a b c d e f : Fin 14)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e) (hef : e < f)
    (h : Pascal556WitnessReuseFin14Strong6Atom χ a b c d e f
      hab hbc hcd hde hef) :
    IsStrongPolygonSet χ {a, b, c, d, e, f} := by
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [Pascal556WitnessReuseFin14Strong6Atom,
    Pascal556WitnessReuseFin14Strong4Atom]

/-- The stronger bounded proposition isolated by causal minimization: the
distinct-witness core needs only the target-avoidance and normalized-cut
clauses, and no witness, probe, first-set, singleton, or anchor clause. -/
def Pascal556WitnessReuseFin14BaseForbidden
    (χ : TripleColoring 14) (cut : Fin 8) : Prop :=
  OneChangeOn χ Finset.univ ∧
    ¬ContainsCapSet χ Finset.univ 5 ∧
    ¬ContainsCupSet χ Finset.univ 5 ∧
    ¬ContainsStrongPolygonSet χ Finset.univ 6 ∧
    ¬ContainsCapSet χ (Pascal556WitnessReuseFin14CutLeft cut) 4 ∧
    ¬ContainsCapSet χ (Pascal556WitnessReuseFin14CutRight cut) 4

/-- Five explicitly ordered left-colored vertices form a cup set. -/
theorem pascal556WitnessReuseFin14_isCupSet_five_of_colors
    (χ : TripleColoring 14) (a b c d e : Fin 14)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (habc : χ ⟨a, b, c, hab, hbc⟩ = Turn.left)
    (habd : χ ⟨a, b, d, hab, hbc.trans hcd⟩ = Turn.left)
    (habe : χ ⟨a, b, e, hab, hbc.trans (hcd.trans hde)⟩ = Turn.left)
    (hacd : χ ⟨a, c, d, hab.trans hbc, hcd⟩ = Turn.left)
    (hace : χ ⟨a, c, e, hab.trans hbc, hcd.trans hde⟩ = Turn.left)
    (hade : χ ⟨a, d, e, hab.trans (hbc.trans hcd), hde⟩ = Turn.left)
    (hbcd : χ ⟨b, c, d, hbc, hcd⟩ = Turn.left)
    (hbce : χ ⟨b, c, e, hbc, hcd.trans hde⟩ = Turn.left)
    (hbde : χ ⟨b, d, e, hbc.trans hcd, hde⟩ = Turn.left)
    (hcde : χ ⟨c, d, e, hcd, hde⟩ = Turn.left) :
    IsCupSet χ {a, b, c, d, e} := by
  rintro ⟨i, j, k, hij, hjk⟩ hi hj hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals assumption

/-- Five explicitly ordered right-colored vertices form a cap set. -/
theorem pascal556WitnessReuseFin14_isCapSet_five_of_colors
    (χ : TripleColoring 14) (a b c d e : Fin 14)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (habc : χ ⟨a, b, c, hab, hbc⟩ = Turn.right)
    (habd : χ ⟨a, b, d, hab, hbc.trans hcd⟩ = Turn.right)
    (habe : χ ⟨a, b, e, hab, hbc.trans (hcd.trans hde)⟩ = Turn.right)
    (hacd : χ ⟨a, c, d, hab.trans hbc, hcd⟩ = Turn.right)
    (hace : χ ⟨a, c, e, hab.trans hbc, hcd.trans hde⟩ = Turn.right)
    (hade : χ ⟨a, d, e, hab.trans (hbc.trans hcd), hde⟩ = Turn.right)
    (hbcd : χ ⟨b, c, d, hbc, hcd⟩ = Turn.right)
    (hbce : χ ⟨b, c, e, hbc, hcd.trans hde⟩ = Turn.right)
    (hbde : χ ⟨b, d, e, hbc.trans hcd, hde⟩ = Turn.right)
    (hcde : χ ⟨c, d, e, hcd, hde⟩ = Turn.right) :
    IsCapSet χ {a, b, c, d, e} := by
  rintro ⟨i, j, k, hij, hjk⟩ hi hj hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals assumption

/-- Four explicitly ordered right-colored vertices form a cap set. -/
theorem pascal556WitnessReuseFin14_isCapSet_four_of_colors
    (χ : TripleColoring 14) (a b c d : Fin 14)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (habc : χ ⟨a, b, c, hab, hbc⟩ = Turn.right)
    (habd : χ ⟨a, b, d, hab, hbc.trans hcd⟩ = Turn.right)
    (hacd : χ ⟨a, c, d, hab.trans hbc, hcd⟩ = Turn.right)
    (hbcd : χ ⟨b, c, d, hbc, hcd⟩ = Turn.right) :
    IsCapSet χ {a, b, c, d} := by
  rintro ⟨i, j, k, hij, hjk⟩ hi hj hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl <;> try omega
  all_goals assumption

end ErdosSzekeres

end
