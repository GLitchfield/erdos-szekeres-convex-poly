module

public import ErdosSzekeres.PredecessorHalfFin13CheckpointSegment255

@[expose] public section

namespace ErdosSzekeres

/-! Public alias for the checkpointed, kernel-checked Fin13 LRAT refutation. -/
run_cmd
  Lean.Elab.Command.liftTermElabM do
    let sourceName :=
      `ErdosSzekeres.PredecessorHalfFin13Checkpoint.publicUnsat
    let targetName :=
      `ErdosSzekeres.predecessorHalfFin13_lrat_unsat
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
