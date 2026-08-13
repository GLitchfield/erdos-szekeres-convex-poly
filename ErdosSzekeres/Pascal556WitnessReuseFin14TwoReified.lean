module

public import ErdosSzekeres.Pascal556WitnessReuseFin14TwoSegment031
public import ErdosSzekeres.Pascal556WitnessReuseFin14Checkpoint

@[expose] public section

namespace ErdosSzekeres

set_option maxHeartbeats 0

lrat_checkpoint_reify Pascal556WitnessReuseFin14TwoContext
  Pascal556WitnessReuseFin14Two.proof
  pascal556WitnessReuseFin14TwoReified
  (include_str "../runs/agents/20260812-promotion-wave/pascal556-lean/two-core.cnf")

end ErdosSzekeres

end
