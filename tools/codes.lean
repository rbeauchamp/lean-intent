import LeanIntent.CodeAudit

/-!
# `codes`: the audit of declared types' codes over the library

`tools/check.lean` runs this program for its rule `CODES`, once it has built the library, as

    lean --run tools/codes.lean <module>...

with `LEAN_PATH` naming the library's build, so that Lean finds `LeanIntent.CodeAudit` and the
modules it is given. It imports those modules and runs `LeanIntent.CodeAudit.audit` from every
constant they declare, printing one line for each reason the audit refuses
(`LeanIntent.CodeAudit.report`). It exits with status `0` when the audit accepts, `1` when it
refuses or when the modules declare no constant, since an audit of nothing would accept anything,
and with another status, through an uncaught error, when it cannot run.
-/

open Lean

def main (args : List String) : IO UInt32 := do
  let mods := args.toArray.map String.toName
  if mods.isEmpty || mods.any (·.isAnonymous) then
    throw <| IO.userError "usage: lean --run tools/codes.lean <module>..."
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map fun m => { module := m }) {}
  let idxs := mods.filterMap env.getModuleIdx?
  let roots := env.constants.map₁.toList.filterMap fun (c, _) =>
    (env.getModuleIdxFor? c).bind fun i => if idxs.contains i then some c else none
  if roots.isEmpty then
    IO.println "the modules declare no constant, so there is nothing to audit"
    return 1
  let (findings, refusal?) ← ((LeanIntent.CodeAudit.audit roots).run' : CoreM _).toIO'
    { fileName := "<codes>", fileMap := default, initHeartbeats := ← IO.getNumHeartbeats } { env }
  let lines := LeanIntent.CodeAudit.report findings refusal?
  for l in lines do
    IO.println l
  return if lines.isEmpty then 0 else 1
