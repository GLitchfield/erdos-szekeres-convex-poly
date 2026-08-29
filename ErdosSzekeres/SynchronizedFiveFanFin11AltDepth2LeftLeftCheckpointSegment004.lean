-- Generated checkpoint source; do not edit.
module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2LeftLeftCheckpointContext
import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2LeftLeftCheckpointSegment000
import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2LeftLeftCheckpointSegment001
import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2LeftLeftCheckpointSegment002
import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2LeftLeftCheckpointSegment003

public section

namespace ErdosSzekeres

set_option maxHeartbeats 1000000000

lrat_checkpoint_segment
  SynchronizedFiveFanFin11AltDepth2LeftLeftCheckpointContext
  SynchronizedFiveFanFin11AltDepth2LeftLeftCheckpoint 4 256
  (include_str "Fin11AltDepth2CheckpointData/LeftLeft/core.cnf")
  (include_str "Fin11AltDepth2CheckpointData/LeftLeft/segment-004.lrat")
  (include_str "Fin11AltDepth2CheckpointData/LeftLeft/carry-input-004.txt")
  (include_str "Fin11AltDepth2CheckpointData/LeftLeft/carry-output-004.txt")

end ErdosSzekeres

end
