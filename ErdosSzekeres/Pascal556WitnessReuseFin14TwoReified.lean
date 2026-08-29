module

public import ErdosSzekeres.Pascal556WitnessReuseFin14TwoSegment031
public import ErdosSzekeres.Pascal556WitnessReuseFin14Checkpoint

@[expose] public section

namespace ErdosSzekeres

set_option maxHeartbeats 0

lrat_checkpoint_reify Pascal556WitnessReuseFin14TwoContext
  Pascal556WitnessReuseFin14Two.proof
  pascal556WitnessReuseFin14TwoReified
  (include_str "../certificates/pascal556-witness-reuse-fin14/two-core.cnf")

end ErdosSzekeres

end
