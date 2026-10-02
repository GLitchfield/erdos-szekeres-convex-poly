import Lean

open Lean

-- Observational audit, not a mathematical theorem. Follow all constants in
-- each declaration's type and value using the same API as the es extractor.
def main (args : List String) : IO Unit := do
  let (mod, root, out) ← match args with
    | [mod, root, out] => pure (mod.toName, root.toName, out)
    | _ => throw (IO.userError "expected MODULE DECLARATION OUTPUT")
  initSearchPath (← findSysroot)
  let started ← IO.monoMsNow
  let env ← importModules #[{ module := mod, importAll := false }] {} 0
  let rootModule := (env.getModuleIdxFor? root).map fun idx =>
    env.header.moduleNames[idx.toNat]!.toString
  let total := env.header.moduleData.foldl (fun n m => n + m.constants.size) 0
  IO.eprintln s!"dependency trace: imported {env.header.moduleData.size} modules; \
    {total} constants are the upper bound on the reachable closure"
  let mut seen : Std.HashSet Name := {}
  let mut stack := #[root]
  let mut modules : Std.HashSet Name := {}
  let mut axioms : Array Name := #[]
  let mut unsafeConstants : Array Name := #[]
  while !stack.isEmpty do
    let name := stack.back!
    stack := stack.pop
    if seen.contains name then continue
    let some info := env.find? name |
      throw (IO.userError s!"missing reachable constant {name}")
    seen := seen.insert name
    if let some idx := env.getModuleIdxFor? name then
      modules := modules.insert env.header.moduleNames[idx.toNat]!
    if info matches .axiomInfo _ then axioms := axioms.push name
    if info.isUnsafe then unsafeConstants := unsafeConstants.push name
    for dep in info.getUsedConstantsAsSet.toArray do
      if !seen.contains dep then stack := stack.push dep
    if seen.size % 1000 == 0 then
      IO.eprintln s!"dependency trace: {seen.size}/{total} visited, \
        {stack.size} pending, {(← IO.monoMsNow) - started} ms elapsed"
  let elapsed := (← IO.monoMsNow) - started
  let result := Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("module", toJson mod.toString),
    ("root", toJson root.toString),
    ("root_module", toJson rootModule),
    ("semantics", toJson "transitive type-and-value constant closure; observational"),
    ("reachable_constants", toJson seen.size),
    ("imported_constant_upper_bound", toJson total),
    ("elapsed_ms", toJson elapsed),
    ("modules", toJson (modules.toArray.map Name.toString)),
    ("axioms", toJson (axioms.map Name.toString)),
    ("unsafe_constants", toJson (unsafeConstants.map Name.toString))]
  IO.FS.writeFile out result.pretty
  IO.eprintln s!"dependency trace complete: {seen.size} reachable in {elapsed} ms"
