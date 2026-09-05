module

public import ErdosSzekeres.ES6AnchoredCheckpointSegment191

@[expose] public section

namespace ErdosSzekeres.ES6

/-! Public alias for the checkpointed, kernel-checked anchored ES(6) refutation. -/
run_cmd
  Lean.Elab.Command.liftTermElabM do
    let sourceName := `ErdosSzekeres.ES6.ES6AnchoredCheckpoint.publicUnsat
    let targetName := `ErdosSzekeres.ES6.es6Anchored_lrat_unsat
    let info ← Lean.getConstInfo sourceName
    Lean.withExporting do
      Lean.addDecl <| .thmDecl {
        name := targetName
        levelParams := info.levelParams
        type := info.type
        value := Lean.mkConst sourceName (info.levelParams.map Lean.mkLevelParam)
      }

end ErdosSzekeres.ES6

end
