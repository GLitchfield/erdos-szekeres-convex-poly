module

public import ErdosSzekeres.Pascal556WitnessReuseFin14Transport

@[expose] public section

namespace ErdosSzekeres

/-- The existing witness-reuse consumer instantiated by the two exact leaves. -/
theorem fiveSingletonResidualProbeImpossible556_of_pascal556Fin14 :
    FiveSingletonResidualProbeImpossible556 :=
  fiveSingletonResidualProbeImpossible556_of_witnessReuseLeaves
    twoFiveSingletonProbeWitnessesImpossible556
    tenProbeFiveSingletonWitnessImpossible556

/-- The existing Pascal-tail consumer closes the exact `(5,5,6)` state. -/
theorem pascalTailTwoSideBound_556 : PascalTailTwoSideBound 5 5 6 :=
  pascalTailTwoSideBound_556_of_fiveSingletonResidualProbeImpossible
    fiveSingletonResidualProbeImpossible556_of_pascal556Fin14

end ErdosSzekeres

end
