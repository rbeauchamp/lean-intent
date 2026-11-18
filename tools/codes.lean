module

import LeanIntent.CodeAudit
import LeanIntent.Imported
meta import LeanIntent.CodeAudit
meta import LeanIntent.Imported

/-!
# `codes`: the audit of declared types' codes over the library

`tools/check.lean` runs this program for its rule `CODES`, once it has built the library, as

    lean --run tools/codes.lean <module>...

with `LEAN_PATH` naming the library's build, so that Lean finds `LeanIntent.CodeAudit`,
`LeanIntent.Imported` and the modules it is given. It is a `module` file: `main` is public, and each
of the two is imported a second time with `meta`, since Lean loads the compiled code of an imported
module, which `lean --run` runs, only where the import says `meta`. It imports the modules it is
given and runs `LeanIntent.CodeAudit.audit` from every constant they declare, printing one line for
each reason the audit refuses (`LeanIntent.CodeAudit.report`).

It imports them with every environment extension's state loaded (`LeanIntent.Imported.loaded`),
because the audit asks Lean what only that state answers: whether a declaration is an instance of a
class, what a definition reduces to, how a type prints and which axioms Lean recorded for a
declaration. `LeanIntent.CodeAudit`'s module comment names the state each question reads. Lean's
plain import leaves that state as it starts, and the audit then names no instance in any refusal,
with no error. Loading runs the `initialize` declarations of the modules given, in this process:
`LeanIntent.Imported`'s module comment says what that admits, and `main` is `unsafe` because that
import is.

It exits with status `0` when the audit accepts, having printed nothing; `1` when it refuses, or
when the modules declare no constant, since an audit of nothing would accept anything, having
printed to standard output a line for each reason; and `2` when it cannot run: any error raised in
`main` (its arguments, a module Lean cannot import, an error the audit throws, a failure to print)
is caught and printed to standard error. Lean ends a program whose `main` raises an error with
status `1`, which would read as a refusal, so `main` never lets one escape.
-/

open Lean

public unsafe def main (args : List String) : IO UInt32 := do
  try
    let mods := args.toArray.map String.toName
    if mods.isEmpty || mods.any (·.isAnonymous) then
      throw <| IO.userError "usage: lean --run tools/codes.lean <module>..."
    initSearchPath (← findSysroot)
    let env ← LeanIntent.Imported.loaded mods
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
