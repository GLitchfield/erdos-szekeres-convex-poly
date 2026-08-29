-- Generated checkpoint source; do not edit.
module

public import ErdosSzekeres.LRATCheckpoint

@[expose] public section

namespace ErdosSzekeres

-- Checkpoint projections are proof infrastructure, not useful premises.
run_cmd
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "SynchronizedFiveFanFin11AltDepth2RightLeftCheckpoint"

lrat_checkpoint_context SynchronizedFiveFanFin11AltDepth2RightLeftCheckpointContext
  (include_str "Fin11AltDepth2CheckpointData/RightLeft/core.cnf")

end ErdosSzekeres

end
