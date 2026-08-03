module

public import ErdosSzekeres.LRATCheckpoint

/-!
# Compact public endpoint for a checkpointed LRAT proof

The ordinary checkpoint command exports every declaration it creates. That is
necessary for carried clauses, but at the final segment it also exposes the
large internal empty-clause proof to downstream legacy imports. This command
keeps all final-segment internals in the private module facet and exports only
an opaque alias with the contradiction theorem's type.
-/

@[expose] public meta section

open Lean Meta

namespace ErdosSzekeres.LRATCheckpoint

open Lean Elab Term Command

elab "lrat_checkpoint_final_segment " context:ident ppSpace root:ident ppSpace segment:num
    ppSpace bundleLimit:num ppSpace cnf:term:max ppSpace lrat:term:max ppSpace carryInput:term:max
    ppSpace carryOutput:term:max : command => do
  let contextName ← liftTermElabM <| resolveGlobalConstNoOverload context
  let rootName := (← getCurrNamespace) ++ root.getId
  let segmentNumber := segment.getNat
  let bundleLimitNumber := bundleLimit.getNat
  liftTermElabM do
    let cnfContents ← unsafe evalTerm String (mkConst ``String) cnf
    let lratContents ← unsafe evalTerm String (mkConst ``String) lrat
    let carryInputContents ← unsafe evalTerm String (mkConst ``String) carryInput
    let carryOutputContents ← unsafe evalTerm String (mkConst ``String) carryOutput
    withoutExporting do
      addSegment contextName rootName segmentNumber bundleLimitNumber cnfContents lratContents
        carryInputContents carryOutputContents
    let privateUnsatName := rootName.str "unsat"
    let privateUnsat ← getConstInfo privateUnsatName
    forallTelescope privateUnsat.type fun arguments conclusion => do
      let badName := rootName.str "bad"
      let badType ← mkForallFVars arguments (mkSort .zero)
      let badValue ← mkLambdaFVars arguments conclusion
      let compactConclusion := mkAppN (mkConst badName) arguments
      let compactType ← mkForallFVars arguments compactConclusion
      withExporting do
        addDecl <| .defnDecl {
          name := badName
          levelParams := privateUnsat.levelParams
          type := badType
          value := badValue
          hints := .regular 0
          safety := .safe
        }
        addDecl <| .thmDecl {
          name := rootName.str "publicUnsat"
          levelParams := privateUnsat.levelParams
          type := compactType
          value := mkConst privateUnsatName (privateUnsat.levelParams.map mkLevelParam)
        }

end ErdosSzekeres.LRATCheckpoint

end
