-- Generated checkpoint leaf; do not edit.
module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2LeftLeftCheckpointSegment255

@[expose] public section

namespace ErdosSzekeres

run_cmd
  Lean.Elab.Command.liftTermElabM do
    let sourceName :=
      `ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2LeftLeftCheckpoint.publicUnsat
    let targetName :=
      `ErdosSzekeres.synchronizedFiveFanFin11_SynchronizedFiveFanFin11AltDepth2LeftLeft_lrat_unsat
    let info ← Lean.getConstInfo sourceName
    Lean.withExporting do
      Lean.addDecl <| .thmDecl {
        name := targetName
        levelParams := info.levelParams
        type := info.type
        value := Lean.mkConst sourceName (info.levelParams.map Lean.mkLevelParam)
      }

end ErdosSzekeres

end
