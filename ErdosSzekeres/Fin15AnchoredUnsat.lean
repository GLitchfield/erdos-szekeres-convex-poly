module

public import ErdosSzekeres.Fin15AnchoredCheckpointSegment255

@[expose] public section

namespace ErdosSzekeres

/-! Public alias for the checkpointed, kernel-checked anchored Fin15 refutation. -/
run_cmd
  Lean.Elab.Command.liftTermElabM do
    let sourceName := `ErdosSzekeres.Fin15AnchoredCheckpoint.publicUnsat
    let targetName := `ErdosSzekeres.fin15Anchored_lrat_unsat
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
