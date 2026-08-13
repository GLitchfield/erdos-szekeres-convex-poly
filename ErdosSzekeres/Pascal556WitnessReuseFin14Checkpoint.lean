module

public import ErdosSzekeres.LRATCheckpoint

/-!
# Proof-only endpoint for the state-556 checkpointed LRAT certificates

The shared checkpoint infrastructure normally also reifies the final CNF into
a large propositional disjunction.  The state-556 semantic bridge consumes the
smaller `Sat.Fmla.proof []` theorem directly, so this endpoint deliberately
exports only that kernel-checked empty-clause proof.
-/

@[expose] public meta section

open Lean
open Std (HashMap)

namespace ErdosSzekeres.LRATCheckpoint

def addFinalProofSegment (contextName root : Name) (cnf lrat carryInput : String) : MetaM Unit :=
    do
  let .success _ (_, clauses) :=
      Mathlib.Tactic.Sat.Parser.parseDimacs ⟨cnf, cnf.startPos⟩
    | throwError "parse CNF failed"
  if clauses.isEmpty then throwError "empty CNF"
  let context := mkConst contextName
  let expandedContext := Mathlib.Tactic.Sat.buildConj clauses 0 clauses.size
  let selfProof := mkApp (mkConst ``Sat.Fmla.subsumes_self) context
  let mut database : HashMap Nat Mathlib.Tactic.Sat.Clause := {}

  let .ok carryClauses := parseCarryManifest carryInput
    | throwError "parse checkpoint carry-input manifest failed"
  for carry in carryClauses do
    database := database.insert carry.id {
      lits := carry.literals
      expr := Mathlib.Tactic.Sat.buildClause carry.literals
      proof := mkConst (clauseName root carry.definingSegment carry.id)
    }

  let .success _ steps := Mathlib.Tactic.Sat.Parser.parseLRAT ⟨lrat, lrat.startPos⟩
    | throwError "parse LRAT segment failed"
  let mut emptyProof : Option Expr := none
  for step in steps do
    match step with
    | .del ids => database := ids.foldl (·.erase ·) database
    | .add id literals proofTrace =>
      for signedReference in proofTrace do
        let reference := signedReference.natAbs
        if 0 < reference ∧ reference ≤ clauses.size ∧ !database.contains reference then
          let original := buildOriginalClause clauses context 0 clauses.size expandedContext
            selfProof (reference - 1)
          database := database.insert reference original
      let clause := Mathlib.Tactic.Sat.buildClause literals
      match Mathlib.Tactic.Sat.buildProofStep database literals proofTrace context clause with
      | .error message => throwError message
      | .ok proof =>
        if literals.isEmpty then
          emptyProof := some proof
        else
          database := database.insert id { lits := literals, expr := clause, proof }

  let some proof := emptyProof
    | throwError "final checkpoint segment did not derive the empty clause"
  addDecl <| .thmDecl {
    name := root.str "proof"
    levelParams := []
    type := mkApp2 (mkConst ``Sat.Fmla.proof) context
      (Mathlib.Tactic.Sat.buildClause #[])
    value := proof
  }

open Lean Elab Term Command

elab "lrat_checkpoint_final_proof " context:ident ppSpace root:ident
    ppSpace cnf:term:max ppSpace lrat:term:max ppSpace carryInput:term:max : command => do
  let contextName ← liftTermElabM <| resolveGlobalConstNoOverload context
  let rootName := (← getCurrNamespace) ++ root.getId
  liftTermElabM do
    let cnfContents ← unsafe evalTerm String (mkConst ``String) cnf
    let lratContents ← unsafe evalTerm String (mkConst ``String) lrat
    let carryInputContents ← unsafe evalTerm String (mkConst ``String) carryInput
    withExporting do
      addFinalProofSegment contextName rootName cnfContents lratContents carryInputContents

/-- Reify an already checkpointed empty-clause proof in a separate process. -/
elab "lrat_checkpoint_reify " context:ident ppSpace proof:ident ppSpace name:ident
    ppSpace cnf:term:max : command => do
  let contextName ← liftTermElabM <| resolveGlobalConstNoOverload context
  let proofName ← liftTermElabM <| resolveGlobalConstNoOverload proof
  let declarationName := (← getCurrNamespace) ++ name.getId
  liftTermElabM do
    let cnfContents ← unsafe evalTerm String (mkConst ``String) cnf
    let .success _ (variableCount, clauses) :=
        Mathlib.Tactic.Sat.Parser.parseDimacs ⟨cnfContents, cnfContents.startPos⟩
      | throwError "parse CNF failed"
    let context := Lean.mkConst contextName
    let expandedContext := Mathlib.Tactic.Sat.buildConj clauses 0 clauses.size
    let (type, value) := Mathlib.Tactic.Sat.buildReify context expandedContext
      (Lean.mkConst proofName) variableCount
    withExporting do
      addDecl <| .thmDecl { name := declarationName, levelParams := [], type, value }

end ErdosSzekeres.LRATCheckpoint

end
