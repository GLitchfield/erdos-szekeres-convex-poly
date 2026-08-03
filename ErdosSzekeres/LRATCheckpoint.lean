module

public import Mathlib.Tactic.Sat.FromLRAT

/-!
# Checkpointed LRAT elaboration

Mathlib's `lrat_proof` command keeps the proof expression for every live
learned clause in one elaborator process.  This module reuses the same proof
constructors but permits a trace to be split across Lean modules.  Learned
clauses referenced by later segments are exported as ordinary opaque theorems;
later segments use those kernel-checked constants instead of retaining the
entire historical expression DAG in memory.

The checkpoint manifests and segment files are untrusted inputs.  Incorrect
data can only make elaboration fail: every emitted declaration is checked by
the Lean kernel against `Mathlib.Tactic.Sat`'s soundness theorems.
-/

@[expose] public meta section

open Lean
open Std (HashMap)

namespace ErdosSzekeres.LRATCheckpoint

structure CarryClause where
  id : Nat
  definingSegment : Nat
  bundleNumber : Nat
  bundleSize : Nat
  bundleIndex : Nat
  literals : Array Int

instance : Inhabited Mathlib.Tactic.Sat.Clause :=
  ⟨{ lits := #[], expr := default, proof := default }⟩

def words (line : String) : Array String :=
  line.split (fun c => c.isWhitespace) |>.filter (not ·.isEmpty) |>.map (·.toString) |>.toArray

def parseNatWord (word : String) : Except String Nat :=
  match word.toNat? with
  | some value => .ok value
  | none => .error s!"expected natural number, got {word}"

def parseIntWord (word : String) : Except String Int :=
  match word.toInt? with
  | some value => .ok value
  | none => .error s!"expected integer, got {word}"

def parseCarryManifest (input : String) : Except String (Array CarryClause) := do
  let mut result := #[]
  for line in input.splitOn "\n" do
    let fields := words line
    if fields.isEmpty then continue
    if fields.size < 6 then
      throw s!"short carry-manifest line: {line}"
    let id ← parseNatWord fields[0]!
    let definingSegment ← parseNatWord fields[1]!
    let bundleNumber ← parseNatWord fields[2]!
    let bundleSize ← parseNatWord fields[3]!
    let bundleIndex ← parseNatWord fields[4]!
    if bundleSize = 0 ∨ bundleSize ≤ bundleIndex then
      throw s!"invalid checkpoint bundle location: {line}"
    let mut literals := #[]
    let mut terminated := false
    for field in fields[5:] do
      let literal ← parseIntWord field
      if literal = 0 then
        terminated := true
        break
      literals := literals.push literal
    unless terminated do
      throw s!"unterminated carry-manifest line: {line}"
    result := result.push {
      id, definingSegment, bundleNumber, bundleSize, bundleIndex, literals
    }
  return result

def parseIdManifest (input : String) : Except String (Array Nat) := do
  let mut result := #[]
  for field in words input do
    result := result.push (← parseNatWord field)
  return result

def segmentName (root : Name) (segment : Nat) : Name :=
  root.str s!"s{segment}"

def bundleName (root : Name) (segment bundle : Nat) : Name :=
  (segmentName root segment).str s!"b{bundle}"

def clauseName (root : Name) (segment id : Nat) : Name :=
  (segmentName root segment).str s!"c{id}"

def clauseProofType (context : Expr) (clause : Mathlib.Tactic.Sat.Clause) : Expr :=
  mkApp2 (mkConst ``Sat.Fmla.proof) context clause.expr

partial def buildBundle (context : Expr)
    (clauses : Array Mathlib.Tactic.Sat.Clause) (start stop : Nat) : Expr × Expr :=
  match stop - start with
  | 0 => panic! "empty checkpoint bundle"
  | 1 => (clauseProofType context clauses[start]!, clauses[start]!.proof)
  | length =>
    let middle := start + length / 2
    let (leftType, leftProof) := buildBundle context clauses start middle
    let (rightType, rightProof) := buildBundle context clauses middle stop
    (mkApp2 (mkConst ``And) leftType rightType,
      mkApp4 (mkConst ``And.intro) leftType rightType leftProof rightProof)

partial def projectBundle (size index : Nat) (bundle : Expr) : Expr :=
  match size with
  | 0 => panic! "empty checkpoint bundle"
  | 1 => bundle
  | length =>
    let middle := length / 2
    if index < middle then
      projectBundle middle index (mkProj ``And 0 bundle)
    else
      projectBundle (length - middle) (index - middle) (mkProj ``And 1 bundle)

partial def buildOriginalClause (clauses : Array (Array Int)) (context : Expr)
    (start stop : Nat) (formula subsumesProof : Expr) (index : Nat) :
    Mathlib.Tactic.Sat.Clause :=
  match stop - start with
  | 0 => panic! "empty original-clause interval"
  | 1 =>
    let clause := formula.appArg!
    {
      lits := clauses[start]!
      expr := clause
      proof := mkApp3 (mkConst ``Sat.Fmla.proof_of_subsumes) context clause subsumesProof
    }
  | length =>
    let middle := start + length / 2
    let leftFormula := formula.appFn!.appArg!
    let rightFormula := formula.appArg!
    if index < middle then
      let leftProof :=
        mkApp4 (mkConst ``Sat.Fmla.subsumes_left) context leftFormula rightFormula subsumesProof
      buildOriginalClause clauses context start middle leftFormula leftProof index
    else
      let rightProof :=
        mkApp4 (mkConst ``Sat.Fmla.subsumes_right) context leftFormula rightFormula subsumesProof
      buildOriginalClause clauses context middle stop rightFormula rightProof index

def addContext (name : Name) (cnf : String) : MetaM Unit := do
  let .success _ (_, clauses) := Mathlib.Tactic.Sat.Parser.parseDimacs ⟨cnf, cnf.startPos⟩
    | throwError "parse CNF failed"
  if clauses.isEmpty then throwError "empty CNF"
  addDecl <| .defnDecl {
    name
    levelParams := []
    type := mkConst ``Sat.Fmla
    value := Mathlib.Tactic.Sat.buildConj clauses 0 clauses.size
    hints := .regular 0
    safety := .safe
  }

def addSegment (contextName root : Name) (segment bundleLimit : Nat)
    (cnf lrat carryInput carryOutput : String) : MetaM Unit := do
  if bundleLimit = 0 then throwError "checkpoint bundle limit must be positive"
  let .success _ (variableCount, clauses) :=
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
          let original := buildOriginalClause clauses context 0 clauses.size expandedContext selfProof
            (reference - 1)
          database := database.insert reference original
      let clause := Mathlib.Tactic.Sat.buildClause literals
      match Mathlib.Tactic.Sat.buildProofStep database literals proofTrace context clause with
      | .error message => throwError message
      | .ok proof =>
        if literals.isEmpty then
          emptyProof := some proof
        else
          database := database.insert id { lits := literals, expr := clause, proof }

  let .ok exports := parseIdManifest carryOutput
    | throwError "parse checkpoint carry-output manifest failed"
  let mut exportedClauses := #[]
  for id in exports do
    let some clause := database[id]?
      | throwError "checkpoint export clause {id} is absent after segment {segment}"
    exportedClauses := exportedClauses.push clause
  unless exportedClauses.isEmpty do
    let mut start := 0
    let mut bundleNumber := 0
    while start < exportedClauses.size do
      let stop := min exportedClauses.size (start + bundleLimit)
      let (bundleType, bundleValue) := buildBundle context exportedClauses start stop
      let currentBundleName := bundleName root segment bundleNumber
      withoutExporting do
        addDecl <| .thmDecl {
          name := currentBundleName
          levelParams := []
          type := bundleType
          value := bundleValue
        }
      for index in [start:stop] do
        let id := exports[index]!
        let clause := exportedClauses[index]!
        addDecl <| .thmDecl {
          name := clauseName root segment id
          levelParams := []
          type := clauseProofType context clause
          value := projectBundle (stop - start) (index - start) (mkConst currentBundleName)
        }
      start := stop
      bundleNumber := bundleNumber + 1

  if let some proof := emptyProof then
    let proofName := root.str "proof"
    addDecl <| .thmDecl {
      name := proofName
      levelParams := []
      type := mkApp2 (mkConst ``Sat.Fmla.proof) context (Mathlib.Tactic.Sat.buildClause #[])
      value := proof
    }
    let (type, value) :=
      Mathlib.Tactic.Sat.buildReify context expandedContext (mkConst proofName) variableCount
    addDecl <| .thmDecl {
      name := root.str "unsat"
      levelParams := []
      type
      value
    }

open Lean Elab Term Command

elab "lrat_checkpoint_context " name:ident ppSpace cnf:term:max : command => do
  let declarationName := (← getCurrNamespace) ++ name.getId
  liftTermElabM do
    let contents ← unsafe evalTerm String (mkConst ``String) cnf
    withExporting do addContext declarationName contents

elab "lrat_checkpoint_segment " context:ident ppSpace root:ident ppSpace segment:num
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
    withExporting do
      addSegment contextName rootName segmentNumber bundleLimitNumber cnfContents lratContents
        carryInputContents carryOutputContents

end ErdosSzekeres.LRATCheckpoint

end
