module

import LeanIntent.CodeAudit
meta import LeanIntent.CodeAudit

open Lean

public def main (args : List String) : IO UInt32 := do
  try
    let mods := args.toArray.map String.toName
    if mods.isEmpty || mods.any (·.isAnonymous) then
      throw <| IO.userError "usage: lean --run tools/codes.lean <module>..."
    initSearchPath (← findSysroot)
    let env ← importModules (mods.map fun m => { module := m }) {}
    let idxs := mods.filterMap env.getModuleIdx?
    let roots := env.constants.map₁.toList.filterMap fun (c, _) =>
      (env.getModuleIdxFor? c).bind fun i => if idxs.contains i then some c else none
    let first :: rest := roots
      | IO.println "the modules declare no constant to audit"
        return 1
    let o ← ((LeanIntent.CodeAudit.audit first rest).run' : CoreM _).toIO'
      { fileName := "<codes>", fileMap := default, initHeartbeats := ← IO.getNumHeartbeats }
      { env }
    let lines := LeanIntent.CodeAudit.report o
    for l in lines do
      IO.println l
    return if lines.isEmpty then 0 else 1
  catch e =>
    try IO.eprintln s!"tools/codes.lean could not run: {e}" catch _ => pure ()
    return 2
