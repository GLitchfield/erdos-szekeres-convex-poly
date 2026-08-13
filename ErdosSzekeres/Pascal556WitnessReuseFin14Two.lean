module

public import ErdosSzekeres.Pascal556WitnessReuseFin14TwoSegment031

@[expose] public section

/-!
# Kernel-checked Fin14 distinct-witness CNF contradiction

This is the exact independently reconstructed normalized CNF layer.  The
separate structural transport to `TwoFiveSingletonProbeWitnessesImpossible556`
must not be conflated with this bounded certificate theorem.
-/

namespace ErdosSzekeres

/-- No propositional valuation satisfies the exact normalized Fin14
distinct-witness counterformula. -/
theorem twoFiveSingletonProbeWitnessesFin14CnfUnsat :
    ¬∃ valuation : Sat.Valuation,
      Sat.Valuation.satisfies_fmla valuation
        Pascal556WitnessReuseFin14TwoContext := by
  rintro ⟨valuation, hsatisfies⟩
  exact Pascal556WitnessReuseFin14Two.proof valuation hsatisfies

end ErdosSzekeres

end
