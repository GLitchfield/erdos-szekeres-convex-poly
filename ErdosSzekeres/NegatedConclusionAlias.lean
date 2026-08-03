module

public import Lean

/-!
# Compact names for large negated theorem conclusions

The command in this module exposes the proposition negated by a theorem under
a short definition, then exports the same proof with that named conclusion.
Both generated declarations are checked by Lean's environment checker.
-/

@[expose] public meta section

open Lean Meta

namespace ErdosSzekeres

open Lean Elab Command

elab "negated_conclusion_alias " proposition:ident proof:ident " from " source:ident : command => do
  let sourceName ← liftTermElabM <| resolveGlobalConstNoOverload source
  let propositionName := (← getCurrNamespace) ++ proposition.getId
  let proofName := (← getCurrNamespace) ++ proof.getId
  liftTermElabM do
    let sourceInfo ← getConstInfo sourceName
    forallTelescope sourceInfo.type fun arguments conclusion => do
      unless conclusion.isAppOfArity ``Not 1 do
        throwError "source theorem must have a negated conclusion"
      unless arguments.size > 0 do
        throwError "source theorem must quantify the proposition parameter"
      let parameter := arguments[0]!
      let body := conclusion.appArg!
      let propositionType ← mkForallFVars #[parameter] (mkSort .zero)
      let propositionValue ← mkLambdaFVars #[parameter] body
      let namedConclusion := mkApp (mkConst propositionName) parameter
      let namedProofType ← mkForallFVars arguments (mkApp (mkConst ``Not) namedConclusion)
      withExporting do
        addDecl <| .defnDecl {
          name := propositionName
          levelParams := sourceInfo.levelParams
          type := propositionType
          value := propositionValue
          hints := .regular 0
          safety := .safe
        }
        addDecl <| .thmDecl {
          name := proofName
          levelParams := sourceInfo.levelParams
          type := namedProofType
          value := mkConst sourceName (sourceInfo.levelParams.map mkLevelParam)
        }

end ErdosSzekeres

end
