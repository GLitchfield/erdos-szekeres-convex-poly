/-
Sequential axiom audit.

  lake env lean --run scripts/AxiomAudit.lean <Module> <constant> [<constant> ...]

`#print axioms` walks a theorem's dependency graph depth first, which for the
project's checkpointed certificates touches ~90 GB of private proof terms in a
random order and thrashes on any machine with less memory than that.  This
script imports the module (with private data) and instead resolves every
constant's axiom set module by module in import order: each module's proof
terms are read once, sequentially, and a constant's set is the union of its
own kind (if it is an axiom) and the sets of the constants it references,
which live in the same module or in an earlier one.  Sets are stored as bit
masks over the axioms encountered, so memory stays small.
-/
import Lean
open Lean

structure Audit where
  axioms   : Array Name := #[]
  axiomIdx : Std.HashMap Name Nat := {}
  taint    : Std.HashMap Name UInt64 := {}   -- absent ⇒ no axioms
  visited  : Std.HashSet Name := {}
  unknown  : Nat := 0                          -- references to constants not found anywhere
  scanned  : Nat := 0

def Audit.axiomBit (a : Audit) (n : Name) : Audit × UInt64 :=
  match a.axiomIdx[n]? with
  | some i => (a, (1 : UInt64) <<< i.toUInt64)
  | none =>
    let i := a.axioms.size
    ({ a with axioms := a.axioms.push n, axiomIdx := a.axiomIdx.insert n i }, (1 : UInt64) <<< i.toUInt64)

def Audit.names (a : Audit) (mask : UInt64) : List Name :=
  (List.range a.axioms.size).filterMap fun i =>
    if (mask >>> i.toUInt64) &&& 1 == 1 then some a.axioms[i]! else none

/-- Resolve all constants of one module.  Iterative depth-first resolution
with an explicit stack; dependencies in earlier modules are already visited. -/
def processModule (consts : Array ConstantInfo) (a : Audit) : Audit := Id.run do
  let mut a := a
  let mut localConsts : Std.HashMap Name ConstantInfo := {}
  for ci in consts do
    localConsts := localConsts.insert ci.name ci
  let mut deps : Std.HashMap Name (Array Name) := {}
  for ci in consts do
    if a.visited.contains ci.name then continue
    let mut stack : Array Name := #[ci.name]
    let mut inProgress : Std.HashSet Name := {}
    while !stack.isEmpty do
      let top := stack.back!
      if a.visited.contains top then
        stack := stack.pop
        continue
      let some info := localConsts[top]? | do
        -- referenced constant not in this module and not visited: unknown
        a := { a with unknown := a.unknown + 1, visited := a.visited.insert top }
        stack := stack.pop
        continue
      let used ← match deps[top]? with
        | some u => pure u
        | none =>
          let u := info.getUsedConstantsAsSet.toArray.filter (· != top)
          deps := deps.insert top u
          pure u
      let pending := used.filter fun d => !a.visited.contains d && !inProgress.contains d && localConsts.contains d
      if pending.isEmpty then
        let mut mask : UInt64 := 0
        if info matches .axiomInfo _ then
          let (a', bit) := a.axiomBit top
          a := a'; mask := mask ||| bit
        for d in used do
          if let some t := a.taint[d]? then mask := mask ||| t
        a := { a with visited := a.visited.insert top, scanned := a.scanned + 1,
                      taint := if mask != 0 then a.taint.insert top mask else a.taint }
        inProgress := inProgress.erase top
        deps := deps.erase top
        stack := stack.pop
      else
        inProgress := inProgress.insert top
        for d in pending do stack := stack.push d
  return a

def main (args : List String) : IO Unit := do
  let some modName := args.head? | throw <| IO.userError "usage: AxiomAudit <Module> <constant>..."
  let targets := args.drop 1
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := modName.toName, importAll := true }] {} 0
  let header := env.header
  IO.eprintln s!"imported {header.moduleData.size} modules"
  let mut a : Audit := {}
  let mut i := 0
  for data in header.moduleData do
    a := processModule data.constants a
    i := i + 1
    if i % 200 == 0 then IO.eprintln s!"  {i} modules, {a.scanned} constants, {a.axioms.size} axioms seen"
  IO.eprintln s!"scanned {a.scanned} constants in {header.moduleData.size} modules; unknown references {a.unknown}; axioms declared: {a.axioms.toList}"
  for t in targets do
    let n := t.toName
    match a.taint[n]? with
    | some mask => IO.println s!"'{t}' depends on axioms: {a.names mask}"
    | none =>
      if a.visited.contains n then IO.println s!"'{t}' depends on axioms: []"
      else IO.println s!"'{t}': not found"
