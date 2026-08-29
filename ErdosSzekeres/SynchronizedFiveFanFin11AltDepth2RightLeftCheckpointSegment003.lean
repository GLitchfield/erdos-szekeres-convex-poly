-- Generated checkpoint source; do not edit.
module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2RightLeftCheckpointContext
import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2RightLeftCheckpointSegment000
import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2RightLeftCheckpointSegment001
import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2RightLeftCheckpointSegment002

public section

namespace ErdosSzekeres

set_option maxHeartbeats 1000000000

lrat_checkpoint_segment
  SynchronizedFiveFanFin11AltDepth2RightLeftCheckpointContext
  SynchronizedFiveFanFin11AltDepth2RightLeftCheckpoint 3 256
  (include_str "Fin11AltDepth2CheckpointData/RightLeft/core.cnf")
  (include_str "Fin11AltDepth2CheckpointData/RightLeft/segment-003.lrat")
  (include_str "Fin11AltDepth2CheckpointData/RightLeft/carry-input-003.txt")
  (include_str "Fin11AltDepth2CheckpointData/RightLeft/carry-output-003.txt")

end ErdosSzekeres

end
