-- Generated checkpoint source; do not edit.
module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2RightLeftCheckpointContext
import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2RightLeftCheckpointSegment000
import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2RightLeftCheckpointSegment001

public section

namespace ErdosSzekeres

set_option maxHeartbeats 1000000000

lrat_checkpoint_segment
  SynchronizedFiveFanFin11AltDepth2RightLeftCheckpointContext
  SynchronizedFiveFanFin11AltDepth2RightLeftCheckpoint 2 256
  (include_str "Fin11AltDepth2CheckpointData/RightLeft/core.cnf")
  (include_str "Fin11AltDepth2CheckpointData/RightLeft/segment-002.lrat")
  (include_str "Fin11AltDepth2CheckpointData/RightLeft/carry-input-002.txt")
  (include_str "Fin11AltDepth2CheckpointData/RightLeft/carry-output-002.txt")

end ErdosSzekeres

end
