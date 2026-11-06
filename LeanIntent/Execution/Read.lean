import Lean
import LeanIntent.Execution
import LeanIntent.Execution.Code
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
| what each declaration's code calls | `irRefs`: the declarations that the IR the build stored for it, as Lean finds it (`IR.findEnvDecl`), calls (`IR.Expr.fap`) or makes a closure of (`IR.Expr.pap`), collected by `bodyRefs`, a match over every constructor of the IR's syntax with no wildcard; none for a declaration with no stored IR or stored as `extern` |
| the implementation's compiled code | `isCompiledCodeOf` (`LeanIntent.Execution.Code`) over the names the environment holds a constant of (`Environment.contains`): the implementation, and each declaration with stored IR that the environment holds no constant of and whose name is that of the implementation's compiled code followed by `_redArg`, the copy reduce-arity makes; no other declaration |
| which declarations can lead to the implementation | those of the modules whose imports reach the module that declares it (`importersOf`, over the imports Lean records of each module, `ModuleData.imports`), a declaration's module being the one Lean attributes it to (`importedModuleOf`, through `Environment.getModuleIdxFor?`) |
| whether `main` reaches the implementation | `Execution.reach` from `main` over what the walk recorded of each declaration reached, with fuel `2 ^ 64` (`reachesIn`); the implementation is asked for by its module and its name, so a constant of the same name in another module is not it |

The walk from `main` records, for each declaration it reaches that can lead to the implementation,
what `irRefs` gives it, and the implementation too where the declaration is the implementation's
compiled code, an entry that stands for "this declaration is the implementation's compiled code"
rather than for a call; it records nothing for any other declaration. `reach` then runs over that
record, so what it reports reached is reached through it (`Execution.reach_reached`), and a
declaration the walk did not record refers to nothing, which can only make a reach unfound. By
`Execution.reaches_prune_iff`, a reach through the declarations kept is a reach through all of them,
given that an IR body calls only declarations of modules its own module's imports reach, which is
trusted. The reader reconstructs no environment extension's state and runs no part of the compiler:
it reads the code the build stored.

## The IR the build stored

The reading relies on these facts about Lean v4.35.0, read from its source:

* `IR.findEnvDecl` (`Lean/Compiler/IR/CompilerM.lean` 142-143) looks a declaration up by its module
  index, in that module's IR entries first and then in its `.olean` entries
  (`Lean/Compiler/LCNF/Basic.lean` 1252-1262); in an environment `importModules` makes, the
  extension's own state is empty (its `addImportedFn`, `CompilerM.lean` 85), so only what the
  modules stored is found.
* A file outside Lean's module system stores every IR declaration in its `.olean` (`CompilerM.lean`
  83-110, the `else entries` branch), which `importModules` reads as its IR
  (`ImportedModule.irData?`, `Lean/Environment.lean` 2046-2054).
* A file of the module system keeps only opaque externs in its `.olean`, and the bodies in its `.ir`
  (`CompilerM.lean` 91-107 and 112-140, `Environment.lean` 1902-1917). `importModules` at its
  default level, `private`, loads the `.ir` of every module it imports (`Environment.lean` 2108-2115
  and 2178-2193). Where a module's `.ir.sig` is missing, it reads the `.olean`'s entries as the IR
  (`Environment.lean` 2094-2100), whose opaque externs have no callees, so the walk can only find
  fewer reaches; where the `.ir.sig` is present and the `.ir` missing, the import fails.
* A declaration the environment holds no constant of gets its module index from the IR's
  `extraConstNames` (`CompilerM.lean` 229-233; `Environment.lean` 1884, 1899 and 2346-2348), so
  `Environment.getModuleIdxFor?` attributes it to the module whose IR entries hold it, the lookup
  `findEnvDecl` makes. `Environment.contains` (`Environment.lean` 1146-1147) reads constants only.
* The IR's syntax is closed: `IR.Expr` (`Lean/Compiler/IR/Basic.lean` 177-206), `IR.Alt` and
  `IR.FnBody` (214-245) and `IR.Decl` (352-355). `bodyRefs` and `irRefs` match every constructor
  without a wildcard, so a constructor a later toolchain adds fails the build of this module.

## The implementation's compiled code

The implementation's compiled code is the implementation `c` and the copies reduce-arity makes of
it (`Execution.isCompiledCodeOf`), and nothing else the compiler makes. Where a declaration has a
parameter its body does not use, reduce-arity names a copy of its body over the parameters it uses
by the declaration's name followed by `_redArg`, and makes the declaration an `@[inline]` wrapper
that calls it, checking no attribute first (`Lean/Compiler/LCNF/ReduceArity.lean` 156-205, lines
172 and 197). The mono phase keeps every parameter, erased type parameters included
(`Lean/Compiler/LCNF/ToMono.lean` 139 and 393), so a polymorphic implementation, or one taking a
proof, is called only through `c._redArg`, and calling that runs `c`'s code. Line 172 is the one
place in Lean's source that makes such a name. The walk counts a declaration as `c`'s copy only
where the environment holds no constant of its name, so a constant of the project named like it
is not counted (`Execution.isCompiledCodeOf_const`), and only where its IR is stored.

No other declaration the compiler makes is counted, and a reach only through one of them is
refused, although the program may run the implementation's code. `docs/execution.md` names the
remedy for each:

* a closed term extracted from `c`'s code, `c._closed_i`, which the compiler caches and shares with
  every later declaration that holds the same term (`Lean/Compiler/LCNF/ExtractClosed.lean`
  216-233), so a declaration that reaches it need not run `c`;
* a lambda lifted out of `c`'s code, reached where a caller inlined `c`: an implementation inlined
  where it is called;
* a specialization of `c` made at a caller, `c._at_.caller.spec_i`
  (`Lean/Compiler/LCNF/Specialize.lean` 315-318). The compiler records its origin in a cache that
  Lean declares private to its module (`Specialize.lean` 30), so this library reads no record of it,
  and the remedy is `@[nospecialize]` on the implementation, under which the compiler specializes
  none of its parameters (`Lean/Compiler/LCNF/SpecInfo.lean` 197-198).

Also refused: an implementation that `implemented_by` or a `csimp` theorem replaces, whose callers'
IR calls the replacement, and one reached only through a module initializer, since `main`'s IR does
not call the initializers. An `@[extern]` implementation is reached where it is called, and its code
in another language is trusted.

What it trusts: that the IR the build stored is the IR it emitted as C, both written by the same
`lean` run, and that the C compiler and Lean's runtime run that code; that an IR body calls only
declarations of modules its own module's imports reach, on which pruning rests; and that a
declaration the environment holds no constant of, named as reduce-arity names its copy of `c`, is
that copy, read at Lean v4.35.0 (`ReduceArity.lean` 172) and to be read again at each upgrade of the
toolchain. Also trusted: the kernel's reduction, as `LeanIntent.Implementation.Read` trusts it; that
the executables given are the project's, each with the root module Lake builds it from; and that the
modules given are all the project's, as the other readers trust. An executable whose root module
Lean cannot import is an error.
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

/-- The declarations the IR expression `e` calls (`IR.Expr.fap`) or makes a closure of
(`IR.Expr.pap`). -/
def exprRefs : IR.Expr → List Name
  | .fap c _ | .pap c _ => [c]
  | .ctor .. | .reset .. | .reuse .. | .proj .. | .uproj .. | .sproj .. | .ap .. | .box ..
  | .unbox .. | .lit .. | .isShared .. => []

/-- The declarations the IR body `b` calls or makes a closure of, in each of its instructions, join
points and alternatives. -/
partial def bodyRefs : IR.FnBody → List Name
  | .vdecl _ _ e b => exprRefs e ++ bodyRefs b
  | .jdecl _ _ v b => bodyRefs v ++ bodyRefs b
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b | .inc _ _ _ _ b
  | .dec _ _ _ _ b | .del _ b => bodyRefs b
  | .case _ _ _ cs => cs.toList.flatMap fun
    | .ctor _ b | .default b => bodyRefs b
  | .ret _ | .jmp _ _ | .unreachable => []

/-- The declarations that the IR the build stored for `n`, as Lean finds it (`IR.findEnvDecl`),
calls or makes a closure of: none where Lean finds no IR for `n`, or where its IR declares it
implemented in another language (`extern`). -/
def irRefs (env : Environment) (n : Name) : List Name :=
  match IR.findEnvDecl env n with
  | some (.fdecl _ _ _ body _) => bodyRefs body
  | some (.extern ..) | none => []

/-- The modules of `env` whose imports reach the module `m`, `m` included: those whose code can
call a declaration of `m`. -/
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

/-- The module of `env` that `n` belongs to, where `env` imports it: the module that declares the
constant `n`, or, for a declaration the environment holds no constant of, the module whose IR holds
it. -/
def importedModuleOf (env : Environment) (n : Name) : Option Name :=
  env.getModuleIdxFor? n |>.bind fun i => env.header.moduleNames[i.toNat]?

/-- **Whether `main` reaches the implementation `c`** in the current environment, through the
declarations each one's stored IR calls or makes a closure of (`irRefs`), followed only through
declarations of modules whose imports reach `c`'s (`importersOf`), since no other can call it. The
declarations are found by a walk from `main` that records what each one's IR calls, and `c` too for
each other declaration with stored IR that is `c`'s compiled code (`isCompiledCodeOf`, over the
environment's constants: a reduce-arity copy of `c`), and the verdict is `Execution.reach` over that
record. An error when more declarations are reached than `2 ^ 64`. -/
def reachesIn (c : Implementation.Constant) : CoreM Bool := do
  let env ← getEnv
  unless importedModuleOf env c.name == some c.module do return false
  let up := importersOf env c.module
  let code (n : Name) : List Name :=
    if n != c.name && isCompiledCodeOf (env.contains ·) c.name n && (IR.findEnvDecl env n).isSome
    then [c.name] else []
  let mut table : Std.HashMap Name (List Name) := {}
  let mut work := [`main]
  repeat
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      unless table.contains n do
        let refs := if (importedModuleOf env n).any up.contains then irRefs env n ++ code n else []
        table := table.insert n refs
        work := refs ++ work
  match reach (fun n => table.getD n []) `main c.name (2 ^ 64) with
  | .reached => return true
  | .unreached => return false
  | .exhausted => throwError "`main` reaches more than 2 ^ 64 declarations"

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
