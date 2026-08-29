-- Generated checkpoint source; do not edit.
module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2RightLeftCheckpointContext

public section

namespace ErdosSzekeres

set_option maxHeartbeats 1000000000

lrat_checkpoint_segment
  SynchronizedFiveFanFin11AltDepth2RightLeftCheckpointContext
  SynchronizedFiveFanFin11AltDepth2RightLeftCheckpoint 0 256
  (include_str "Fin11AltDepth2CheckpointData/RightLeft/core.cnf")
  (include_str "Fin11AltDepth2CheckpointData/RightLeft/segment-000.lrat")
  (include_str "Fin11AltDepth2CheckpointData/RightLeft/carry-input-000.txt")
  (include_str "Fin11AltDepth2CheckpointData/RightLeft/carry-output-000.txt")

end ErdosSzekeres

end
