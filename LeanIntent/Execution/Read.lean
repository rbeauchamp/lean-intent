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
| what each constant's code mentions | `codeRefs`: for a constant marked `extern`, none; for one with an initializer (`getInitFnNameFor?`), the function that computes it; for one `implemented_by` names a replacement for, the replacement; for one the code generator makes no code for (`Compiler.LCNF.shouldGenerateCode`), none; otherwise the constants of the code `Compiler.LCNF.toDecl` makes of it, the code generator's own first translation, in which types and proofs are erased, run with the state of each environment extension it reads set as below |
| the state of the extensions the translation reads | `importModules` leaves the state of every environment extension at its initial value (it is not given `loadExts`) and loads each imported module's own entries; the reader makes, through each extension's own import function (`addImportedFn`) as Lean's separate code generator `leanir` does, the matchers of every module (`Meta.Match.Extension`), and, for each constant it translates, the `csimp` replacements (`Compiler.CSimp.ext`) and the reducibility settings of other modules' constants (`reducibilityExtraExt`) in force where that constant's module was compiled (`compiledIn`), or refuses, as the next paragraphs state |
| which constants can lead to the implementation | those of the modules whose imports reach the module that declares it (`importersOf`, over the imports Lean records of each module, `ModuleData.imports`); a constant's code mentions only constants of the modules its own imports reach, so no other can, and their code is not read |
| whether `main` reaches the implementation | `Execution.reach` from `main` over what the walk recorded of each constant reached, with fuel `2 ^ 64` (`reachesIn`); the implementation is asked for by its module and its name, so a constant of the same name in another module is not it |

The walk from `main` records, for each constant it reaches, what `codeRefs` gives it where the
constant can lead to the implementation, and nothing otherwise; `reach` then runs over that record,
so what it reports reached is reached through it (`Execution.reach_reached`), and a constant the
walk did not record refers to nothing, which can only make a reach unfound. By
`Execution.reaches_prune_iff`, a reach through the constants kept is a reach through all of them,
given the fact about Lean's environments stated above, which is trusted.

## What the translation reads of environment extensions

These are the queries of an extension's state, rather than of the constants or of an imported
module's own entries, that `codeRefs` makes through `toDecl` and `shouldGenerateCode`, found by
reading their source at Lean v4.35.0 and what they call; the other queries concern imported
constants, which Lean answers from the entries of the module that declares each
(`getModuleEntries`), loaded by `importModules` either way.

* `csimp` replacements. The translation makes them only where it reaches an application of a
  replaced constant (`Lean/Compiler/LCNF/ToLCNF.lean` 534-538, the one call of
  `CSimp.replaceConstant?` under `Lean/Compiler/LCNF`), following each replacement's own, and reads
  them from the extension's state (`Lean/Compiler/CSimpAttr.lean` 82-90). Where a constant of
  module `m` was compiled, every global replacement of the modules `m` imported with their data was
  in force; one that `m` itself declares only if declared above the constant; a `scoped` one only
  if its namespace was open there; and none of a module `m` does not import, however the root
  imports it. `compiledIn` reads which modules `m` imported with their data (`importedBy`, over
  `ModuleData.imports`: all those its imports reach for a module outside Lean's module system; for
  a module of it, those reached by an import followed only by `public` imports, which
  `importModulesCore` loads with their data, `Lean/Environment.lean` 2178-2193), and `settle` gives
  the replacements of those modules as in force, and as open each one `m` declares, each `scoped`
  one, each of a module `m`'s imports reach that it may have imported without its data, and those
  of a constant that two of those modules replace differently, since the build does not record
  their order. `codeRefs` makes the state from the ones in force, through the extension's own
  import function, and when some are open it runs the translation with each open replacement's
  target replaced by `probe`, a name no constant has. The translation is a deterministic run that
  reads a replacement only when it reaches an application of the constant replaced, so a run that
  reaches none of the open ones is the same run whichever of them were in force, and its result is
  the translation the build made; and one that reaches one fails there, since the code generator
  cannot translate an application of a constant the environment lacks (`getCtorArity?`, which
  `visitAppCore` asks just after the replacement, reads the constant). So when the run with
  `probe` fails and the run without it succeeds, `codeRefs` refuses, naming the constant, its
  module and each open replacement's theorem; when both fail, the error of the run without it
  stands. Since a theorem of a module `m` imports mentions only constants of the modules its own
  imports reach, a replacement in force for a constant of `m` is a constant of a module `m`'s
  imports reach, so the fact about modules that pruning relies on holds with replacements made.
* Matchers. The translation reads `Meta.getMatcherInfo?` (`Lean/Meta/Match/MatcherInfo.lean`
  141-145, the extension's state) to expand a matcher where it is applied and make no code of its
  own, and Lean's reduction reads it to reduce a matcher in a type. Each entry is keyed by its
  matcher and is added by the module that declares the matcher, just after declaring it
  (`Lean/Meta/Match/Match.lean` 1116-1126, `Lean/Meta/Constructions/CasesOnSameCtor.lean`
  223-225), so the state made from the entries of every module, which `executableIn` sets as
  `leanir` does, answers for every matcher a constant's translation can reach, one of its module
  declared above it or of a module it imports, as it was answered where that constant was compiled.
* Reducibility settings, which decide whether Lean's reduction unfolds a definition in a type
  (`getReducibilityStatusCore`, `Lean/ReducibilityAttrs.lean` 79-88): a module's settings of its
  own constants are its own entries, and those of other modules' constants are the state of
  `reducibilityExtraExt`, which `codeRefs` makes as for `csimp`. A run cannot tell which of these
  the translation read, so where one is open, `codeRefs` refuses the constant, naming it, its
  module and each open setting.
* The states that Lean's test of definitional equality reads, among them unification hints
  (`Lean/Meta/UnificationHint.lean` 105), classes and instances, stay at their initial values:
  none. The translation's reduction tests definitional equality only to reduce a recursor of an
  inductive family such as `Eq` applied to a proof that is not a constructor
  (`toCtorWhenK`, `Lean/Meta/WHNF.lean` 138-159), and it uses what reduction finds only to decide
  which parts of the code are proofs or types, which it erases, which arguments of a `noConfusion`
  are distinct constructors, how far to eta-expand, and the types of the code.
* `baseTypeExt` (`Lean/Compiler/LCNF/BaseTypes.lean` 20-29) holds the code generator's type of
  each constant, computed from its type when first asked, so its initial state only has it
  computed again.

What it trusts: Lean's code generator, that the code `toDecl` makes of each constant, given the
states above, mentions the constants the compiled program calls; and that the states it leaves at
their initial values do not change what the translation of a constant here mentions. That is not
established: where the build reduced such a recursor inside a type only with the help of a
unification hint, a class or an instance, the reader reduces less, and can keep, and so record the
constants of, a proof or a type that the build erased. Also trusted, because no `.olean` records
them: replacements and reducibility settings marked `local`, which a module puts in its own state
only (`ScopedEnvExtension.addCore`, `Lean/ScopedEnvExtension.lean` 195-199); and that each module
was compiled where it was elaborated, not by `leanir` under the experimental option
`compiler.postponeCompile`, which makes every replacement a module declares, wherever declared, and
no reducibility setting of another module, part of each of its constants' compilation
(`src/LeanIR.lean` 94-136). Also trusted: the kernel's reduction, as
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

/-- The modules that module `m` of `env` imports, directly or through others (`all`), and those of
them whose data, attributes included, the compilation of `m` imported for certain (`loaded`). -/
structure Imported where
  all : Std.HashSet Name := {}
  loaded : Std.HashSet Name := {}

/-- What module `m` of `env` imports, read from the imports Lean records of each module
(`ModuleData.imports`): every module its imports reach, all loaded with their data for a module
outside Lean's module system; for a module of it, those reached by an import followed only by
`public` imports are loaded with their data whatever the level (`importModulesCore`), and an
`import all` can load others, which are not counted as loaded. -/
def importedBy (env : Environment) (m : Name) : Imported := Id.run do
  let data (n : Name) := env.getModuleIdx? n >>= fun i => env.header.moduleData[i.toNat]?
  let imports (n : Name) : List Import := ((data n).map (·.imports.toList)).getD []
  let isModule := (data m).any (·.isModule)
  let mut out : Imported := {}
  let mut work := (imports m).map (·.module, true)
  repeat
    match work with
    | [] => break
    | (n, loaded) :: rest =>
      work := rest
      unless out.all.contains n && (!loaded || out.loaded.contains n) do
        out := { all := out.all.insert n
                 loaded := if loaded then out.loaded.insert n else out.loaded }
        work := (imports n).map (fun i => (i.module, loaded && (i.isExported || !isModule))) ++ work
  return out

/-- What the build records of the scoped extension `ext` where a constant of module `m` was
compiled, given what `m` imports: the entries of the modules `m` imported with their data for
certain, by module in the order of `env`'s modules, all the entries in force there for certain; and,
each with its module, the entries whose being in force there the build leaves open: every entry of
`m` itself, since the build does not record where in `m` it was declared; every `scoped` entry,
since it does not record which namespaces were open; every entry of a module `m` imports whose
data it may not have imported; and the entries of a key to which the modules imported for certain
give different values, since it does not record their order there. -/
def settle {α σ κ ν : Type} [Inhabited σ] [BEq κ] [Hashable κ] [BEq ν]
    (ext : ScopedEnvExtension α α σ) (env : Environment) (m : Name) (imported : Imported)
    (key : α → κ) (value : α → ν) :
    Array (Array (ScopedEnvExtension.Entry α)) × Array (Name × α) := Id.run do
  let names := env.header.moduleNames
  let mut certain := #[]
  let mut undecided := #[]
  let mut byKey : Std.HashMap κ (Array (Name × α)) := {}
  for h : i in [0:names.size] do
    let n := names[i]
    let entries := ext.ext.getModuleEntries env i
    let sure := imported.loaded.contains n
    certain := certain.push (if sure then entries else #[])
    for e in entries do
      match e with
      | .global a =>
        if n == m || (imported.all.contains n && !sure) then undecided := undecided.push (n, a)
        else if sure then byKey := byKey.insert (key a) ((byKey.getD (key a) #[]).push (n, a))
      | .scoped _ a =>
        if n == m || imported.all.contains n then undecided := undecided.push (n, a)
  for (_, given) in byKey.toArray do
    if let some (_, a) := given[0]? then
      if given.any (value ·.2 != value a) then undecided := undecided ++ given
  return (certain, undecided)

/-- What the build records of where the constants of `module` were compiled (`settle`): the `csimp`
replacements (`Compiler.CSimp.ext`) and the reducibility settings of constants of other modules
(`reducibilityExtraExt`), each by the entries in force for certain and those left open. -/
structure Compiled where
  module : Name
  csimp : Array (Array (ScopedEnvExtension.Entry Compiler.CSimp.Entry))
  undecidedCSimp : Array (Name × Compiler.CSimp.Entry)
  reducibility : Array (Array (ScopedEnvExtension.Entry (Name × ReducibilityStatus)))
  undecidedReducibility : Array (Name × Name × ReducibilityStatus)
  deriving Inhabited

/-- What the build records of where the constants of module `m` of `env` were compiled. -/
def compiledIn (env : Environment) (m : Name) : Compiled :=
  let imported := importedBy env m
  let (csimp, undecidedCSimp) :=
    settle Compiler.CSimp.ext env m imported (·.fromDeclName) (·.toDeclName)
  let (reducibility, undecidedReducibility) :=
    settle reducibilityExtraExt env m imported (·.1) (·.2)
  { module := m, csimp, undecidedCSimp, reducibility, undecidedReducibility }

/-- Sets the state of `ext` in the current environment to what the extension's own import function
makes of `entries`, by module, as Lean's separate code generator `leanir` sets the states it needs
(`src/LeanIR.lean` at v4.35.0). -/
def install {α β σ : Type} [Inhabited σ] (ext : PersistentEnvExtension α β σ)
    (entries : Array (Array α)) : CoreM Unit := do
  let env ← getEnv
  let s := ext.toEnvExtension.getState env
  let state ← (ext.addImportedFn entries { env, opts := ← getOptions } : IO σ)
  setEnv <| ext.toEnvExtension.setState (asyncMode := .sync) env { s with state }

/-- A name that the probes of `codeRefs` give as a replacement, which no constant of the
environment may have. -/
def probe : Name := `_lean_intent_execution_probe

/-- **The constants the code of `c` mentions**, as Lean's code generator reads its declaration from
the environment where `c`'s module `cx.module` was compiled (`cx`), before any optimization: none
for a constant implemented in another language (`extern`), the function that computes it for one
computed when the program starts (`init`), the constant that replaces it for one `implemented_by`
names, none for a constant the code generator makes no code for (`Compiler.LCNF.shouldGenerateCode`:
a type, a proof, a constant with no value, a matcher or `casesOn`, which are expanded where they are
used, or a `macro_inline` constant, which is), and otherwise the constants of the code
`Compiler.LCNF.toDecl` makes of it, in which types and proofs are erased, the `_unsafe_rec`
definition of a recursive or `partial` constant stands for it, matchers and `macro_inline` constants
are expanded, and the `csimp` replacements in force where `cx.module` was compiled are made, with
the reducibility settings in force there. An error when the build leaves open a reducibility setting
there, or a `csimp` replacement that the translation reaches: the translation is run with each
open replacement's target replaced by `probe`, which no constant has, so that it fails when it
reaches one, and a failure the run without them does not have is that. -/
def codeRefs (cx : Compiled) (c : Name) : CoreM (List Name) := do
  let env ← getEnv
  if isExtern env c then return []
  if let some f := getInitFnNameFor? env c then
    return if f.isAnonymous then [] else [f]
  if let some g := Compiler.getImplementedBy? env c then return [g]
  unless cx.undecidedReducibility.isEmpty do
    throwError "the code of {c}, a constant of {cx.module}, is translated with reducibility \
      settings that the build does not record as in force or not where {cx.module} was compiled: \
      {cx.undecidedReducibility.toList.map fun (m, d, s) => m!"{s.toAttrString} {d} of {m}"}"
  let translate (probes : Bool) : CoreM (List Name) := withoutModifyingEnv do
    let replaced := if probes then
        #[cx.undecidedCSimp.map fun (_, e) =>
          ScopedEnvExtension.Entry.global { e with toDeclName := probe, thmName := probe }]
      else #[]
    install Compiler.CSimp.ext.ext (cx.csimp ++ replaced)
    install reducibilityExtraExt.ext cx.reducibility
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
  if cx.undecidedCSimp.isEmpty then return ← translate false
  if env.contains probe then throwError "the environment has a constant named {probe}"
  try translate true catch _ =>
    discard <| translate false
    throwError "the code of {c}, a constant of {cx.module}, depends on whether a `csimp` \
      replacement was in force where {cx.module} was compiled, which the build does not record: \
      {cx.undecidedCSimp.toList.map fun (m, e) =>
        m!"{e.thmName} of {m}, which replaces {e.fromDeclName} by {e.toDeclName}"}"

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
each one's code mentions where its module was compiled (`codeRefs`, given `compiledIn` of that
module), followed only through constants of modules whose imports reach `c`'s (`importersOf`),
since no other can mention it. The constants are found by a walk from `main` that records what each
one's code mentions, and the verdict is `Execution.reach` over that record. An error when more
constants are reached than `2 ^ 64`, or when `codeRefs` gives one. -/
def reachesIn (c : Implementation.Constant) : CoreM Bool := do
  let env ← getEnv
  unless importedModuleOf env c.name == some c.module do return false
  let up := importersOf env c.module
  let mut compiled : Std.HashMap Name Compiled := {}
  let mut table : Std.HashMap Name (List Name) := {}
  let mut work := [`main]
  repeat
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      unless table.contains n do
        let mut refs : List Name := []
        if let some m := importedModuleOf env n then
          if up.contains m then
            unless compiled.contains m do compiled := compiled.insert m (compiledIn env m)
            refs ← codeRefs compiled[m]! n
        table := table.insert n refs
        work := refs ++ work
  match reach (fun n => table.getD n []) `main c.name (2 ^ 64) with
  | .reached => return true
  | .unreached => return false
  | .exhausted => throwError "`main` reaches more than 2 ^ 64 constants"

/-- What the build shows of the executable `name`, whose root module is `root`, in the
environment `env` of that module and what it imports: whether `env` declares `main`, and which of
the implementations `targets` it reaches, with the matchers of every module of `env` set
(`Meta.Match.Extension`) as `leanir` sets them. -/
def executableIn (env : Environment) (name root : Name) (targets : List Implementation.Constant) :
    CoreM Executable := do
  let entry := env.contains `main
  let matchers : PersistentEnvExtension _ _ _ := Meta.Match.Extension.extension
  install matchers (matchers.toEnvExtension.getState env).importedEntries
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
