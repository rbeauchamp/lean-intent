import Lean
import LeanIntent.Execution
import LeanIntent.Implementation.Read

/-!
# Reading what a project's executables run from the finished build

`LeanIntent.Execution` decides whether each executable a project says runs a deliverable reaches
the deliverable's recorded implementation from its entry point, given what the build shows. This
module reads all of it from Lean's environment, through Lean's own mechanisms, and parses no source
text:

| Input | How it is read |
|---|---|
| the project's deliverables | as `LeanIntent.Confirmation.Read.check` reads them, from the modules given |
| the implementation recorded for each, and those declared awaiting theirs | `LeanIntent.Implementation.Read.check` of the same modules, its `implementations` and `awaiting` |
| the claims | every constant of those modules whose type reduces, unfolding every definition, to `LeanIntent.Runs _` (`Confirmation.Read.declaredIn`, which refuses an unsafe or partial one); the deliverable its type names, where that is a constant once its metadata is removed; and its value, reduced by the kernel (`Render.readWhnf`) to `Runs.mk`'s application, whose executable the kernel must reduce to a name built of `Name.anonymous`, `Name.str` and `Name.num` with literals (`nameLit`); anything else is an error naming the value |
| the executables | the names and root modules the caller gives, which `LeanIntent.Execution.lakeExecutables` reads from the project's Lake configuration |
| an executable's entry point | the constant `main` of the environment Lean imports from the executable's root module alone (`importModules`), which holds that module and what it imports and nothing else; Lean's code generator writes the program's entry point for the module of those that declares `main`, and two of them cannot both declare it |
| what each constant's code mentions | `codeRefs`: for a constant marked `extern`, none; for one with an initializer (`getInitFnNameFor?`), the function that computes it; for one `implemented_by` names a replacement for, the replacement; for one the code generator makes no code for (`Compiler.LCNF.shouldGenerateCode`), none; otherwise the constants of the code `Compiler.LCNF.toDecl` makes of it, the code generator's own first translation, in which types and proofs are erased |
| which constants can lead to the implementation | those of the modules whose imports reach the module that declares it (`importersOf`, over the imports Lean records of each module, `ModuleData.imports`); a constant's code mentions only constants of the modules its own imports reach, so no other can, and their code is not read |
| whether `main` reaches the implementation | `Execution.reach` from `main` over what the walk recorded of each constant reached, with fuel `2 ^ 64` (`reachesIn`); the implementation is asked for by its module and its name, so a constant of the same name in another module is not it |

The walk from `main` records, for each constant it reaches, what `codeRefs` gives it where the
constant can lead to the implementation, and nothing otherwise; `reach` then runs over that record,
so what it reports reached is reached through it (`Execution.reach_reached`), and a constant the
walk did not record refers to nothing, which can only make a reach unfound. By
`Execution.reaches_prune_iff`, a reach through the constants kept is a reach through all of them,
given the fact about Lean's environments stated above, which is trusted.

What it trusts: Lean's code generator, that the code `toDecl` makes of each constant here, in the
environment of the executable's root module, mentions the constants the compiled program calls. It
can differ where a `csimp` theorem that the root's imports hold was not imported where the constant
was compiled, since such a theorem replaces a constant, by one proved equal to it, only where it is
imported. Such a replacement can also break the fact about modules that pruning relies on; where
that fact fails, the walk can only leave a reach unfound, since every constant it records as
mentioned is one `codeRefs` gives. Also trusted: the kernel's reduction, as
`LeanIntent.Implementation.Read` trusts it; that the executables given are the project's, each with
the root module Lake builds it from; and that the modules given are all the project's, as the other
readers trust. An executable whose root module Lean cannot import is an error.
-/

namespace LeanIntent.Execution.Read

open Lean Meta LeanIntent.Render LeanIntent.Confirmation.Read

/-- The name `e` reduces to, through the kernel: `Name.anonymous`, or `Name.str` or `Name.num`
applied to a name and a literal. An error when it reduces to anything else. -/
partial def nameLit (e : Expr) : MetaM Name := do
  let e ← readWhnf e
  if e.isConstOf ``Name.anonymous then
    return .anonymous
  else if e.isAppOfArity ``Name.str 2 then
    return .str (← nameLit e.appFn!.appArg!) (← strLit e.appArg!)
  else if e.isAppOfArity ``Name.num 2 then
    match ← readWhnf e.appArg! with
    | .lit (.natVal n) => return .num (← nameLit e.appFn!.appArg!) n
    | n => throwError "expected a natural number literal, found{indentExpr n}"
  else throwError "expected a name, found{indentExpr e}"

/-- What the build shows of the value `decl`, a constant whose type reduces to `Runs d`: the
deliverable its type names, where that is a constant, and the executable it names. An error when
its value does not reduce to `Runs.mk`'s application, or the executable to a name. -/
def claimOf (decl : Name) : MetaM Claim := do
  let t ← readWhnf (← getConstInfo decl).type
  unless t.isAppOfArity ``Runs 2 do
    throwError "the type of {decl} is not `LeanIntent.Runs` applied to a deliverable"
  let args ← ctorArgs (← Confirmation.Read.constOf decl) ``Runs.mk 3
  let executable ← try nameLit args[2]! catch e =>
    throwError "the executable {decl} names is not read as a name: {e.toMessageData}"
  return ⟨decl, Implementation.Read.constOf? t.appArg!, executable⟩

/-- The values of `Runs d` the modules `mods` declare, as the build shows them. -/
def claims (mods : Array Name) : MetaM (Array Claim) := do
  (← declaredIn mods ``Runs).mapM claimOf

/-- **The constants the code of `c` mentions**, as Lean's code generator reads its declaration from
the environment, before any optimization: none for a constant implemented in another language
(`extern`), the function that computes it for one computed when the program starts (`init`), the
constant that replaces it for one `implemented_by` names, none for a constant the code generator
makes no code for (`Compiler.LCNF.shouldGenerateCode`: a type, a proof, a constant with no value,
a matcher or `casesOn`, which are expanded where they are used, or a `macro_inline` constant, which
is), and otherwise the constants of the code `Compiler.LCNF.toDecl` makes of it, in which types and
proofs are erased, the `_unsafe_rec` definition of a recursive or `partial` constant stands for it,
`csimp` replacements are made and matchers and `macro_inline` constants are expanded. -/
def codeRefs (c : Name) : CoreM (List Name) := do
  let env ← getEnv
  if isExtern env c then return []
  if let some f := getInitFnNameFor? env c then
    return if f.isAnonymous then [] else [f]
  if let some g := Compiler.getImplementedBy? env c then return [g]
  unless ← Compiler.LCNF.shouldGenerateCode c do return []
  let decl ← (Compiler.LCNF.toDecl c).run
  let ((), out) := (decl.value.forCodeM (m := StateM (Array Name)) fun code => code.forM fun k =>
    match k with
    | .let d _ =>
      match d.value with
      | .const n .. => modify (·.push n)
      | _ => pure ()
    | _ => pure ()).run #[]
  return out.toList

/-- The modules of `env` whose imports reach the module `m`, `m` included: those whose code can
mention a constant `m` declares. -/
def importersOf (env : Environment) (m : Name) : Std.HashSet Name := Id.run do
  let names := env.header.moduleNames
  let mut importers : Std.HashMap Name (Array Name) := {}
  for h : i in [0:names.size] do
    for imp in (env.header.moduleData[i]?.map (·.imports)).getD #[] do
      importers := importers.insert imp.module
        ((importers.getD imp.module #[]).push names[i])
  let mut found : Std.HashSet Name := {}
  let mut work := [m]
  repeat
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      unless found.contains n do
        found := found.insert n
        work := (importers.getD n #[]).toList ++ work
  return found

/-- The module that declares `c` in `env`, where `env` imports it. -/
def importedModuleOf (env : Environment) (c : Name) : Option Name :=
  env.getModuleIdxFor? c |>.bind fun i => env.header.moduleNames[i.toNat]?

/-- **Whether `main` reaches the constant `c`** in the current environment, through the constants
each one's code mentions (`codeRefs`), followed only through constants of modules whose imports
reach `c`'s (`importersOf`), since no other can mention it. The constants are found by a walk from
`main` that records what each one's code mentions, and the verdict is `Execution.reach` over that
record. An error when more constants are reached than `2 ^ 64`. -/
def reachesIn (c : Implementation.Constant) : CoreM Bool := do
  let env ← getEnv
  unless importedModuleOf env c.name == some c.module do return false
  let up := importersOf env c.module
  let keep := fun (n : Name) => (importedModuleOf env n).any up.contains
  let mut table : Std.HashMap Name (List Name) := {}
  let mut work := [`main]
  repeat
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      unless table.contains n do
        let refs ← if keep n then codeRefs n else pure []
        table := table.insert n refs
        work := refs ++ work
  match reach (fun n => table.getD n []) `main c.name (2 ^ 64) with
  | .reached => return true
  | .unreached => return false
  | .exhausted => throwError "`main` reaches more than 2 ^ 64 constants"

/-- What the build shows of the executable `name`, whose root module is `root`, in the
environment `env` of that module and what it imports: whether `env` declares `main`, and which of
the implementations `targets` it reaches. -/
def executableIn (env : Environment) (name root : Name) (targets : List Implementation.Constant) :
    CoreM Executable := do
  let entry := env.contains `main
  let reached ← if entry then targets.filterM reachesIn else pure []
  return ⟨name, root, entry, reached⟩

/-- **What a gate reads**, from the finished build: the report on what the executables `exes`,
each given by its name and root module as the project's Lake configuration declares them, run of
the project whose modules are `mods`. It reads the deliverables and claims of those modules, the
implementations `Implementation.Read.check` reads of them, and, for each executable, the
environment Lean imports from its root module alone, in which it reads `main` and what `main`
reaches. Its findings are empty exactly when every claim holds (`Execution.findings_eq_nil_iff`). -/
def check (mods : Array Name) (exes : Array (Name × Name)) : MetaM Report := do
  let ds ← declaredIn mods ``Deliverable
  let implemented ← Implementation.Read.check mods
  let is := implemented.implementations.map fun (d, _, c) => (d, c)
  let as := implemented.awaiting.map (·.1)
  let cls ← claims mods
  let ctx ← readThe Core.Context
  let es ← exes.mapM fun (name, root) => do
    let targets := (cls.toList.filter (·.executable == name)).flatMap fun cl =>
      is.filterMap fun (d, c) => if cl.deliverable == some d then some c else none
    try
      let env ← importModules #[{ module := root }] (← getOptions)
      let (e, _) ← (executableIn env name root targets.eraseDups).run ctx { env }
      return e
    catch err =>
      throwError "the executable {name}, whose root module is {root}, cannot be read: \
        {err.toMessageData}"
  return report ds.toList is as es.toList cls.toList

end LeanIntent.Execution.Read
