module

public import Lean
public import LeanIntent.Execution
public import LeanIntent.Execution.Code
public import LeanIntent.Implementation.Read
public import LeanIntent.Imported

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
| what the build stored of an executable | `LeanIntent.Imported.stored` of the executable's root module alone: Lean's import of that module and what it imports and nothing else, read into the four questions of a `LeanIntent.Imported.Stored`, which is all this reader has of it |
| an executable's entry point | whether those modules hold a constant `main` (`Stored.contains`, which is `Environment.contains`); Lean's code generator writes the program's entry point for the module of those that declares `main`, and two of them cannot both declare it |
| what each declaration's code calls | `irRefs`: the declarations that the IR the build stored for it, as Lean finds it (`Stored.irDecl?`, which is `IR.findEnvDecl`), calls (`IR.Expr.fap`) or makes a closure of (`IR.Expr.pap`), collected by `bodyRefs`, a match over every constructor of the IR's syntax with no wildcard; none for a declaration with no stored IR or stored as `extern` |
| the implementation's compiled code | `isCompiledCodeOf` (`LeanIntent.Execution.Code`) over the names the modules hold a constant of (`Stored.contains`): the implementation, and each declaration with stored IR that the modules hold no constant of and whose name is that of the implementation's compiled code followed by `_redArg`, the copy reduce-arity makes; no other declaration |
| which declarations can lead to the implementation | those of the modules whose imports reach the module that declares it (`importersOf`, over the imports Lean records of each module, `Stored.modules`, which is `ModuleData.imports`), a declaration's module being the one Lean attributes it to (`Stored.moduleOf`, through `Environment.getModuleIdxFor?`) |
| whether `main` reaches the implementation | `Execution.reach` from `main` over what the walk recorded of each declaration reached, with fuel `2 ^ 64` (`reachesIn`); the implementation is asked for by its module and its name, so a constant of the same name in another module is not it |

The walk from `main` records, for each declaration it reaches that can lead to the implementation,
what `irRefs` gives it, and the implementation too where the declaration is the implementation's
compiled code, an entry that stands for "this declaration is the implementation's compiled code"
rather than for a call; it records nothing for any other declaration. `reach` then runs over that
record, so what it reports reached is reached through it (`Execution.reach_reached`), and a
declaration the walk did not record refers to nothing, which can only make a reach unfound. By
`Execution.reaches_prune_iff`, a reach through the declarations kept is a reach through all of them,
given that an IR body calls only declarations of modules its own module's imports reach, which is
trusted. The reader runs no part of the compiler: it reads the code the build stored.

## The two environments, and what each question reads

This reader asks Lean questions of two environments. Of the one it imports itself, no question is
answered from an environment extension's state; of the one it runs in, it asks nothing unless
that state is loaded.

* **The environment it runs in**, from which it reads the deliverables, the implementations and
  the claims, as the first three rows above say. `check` runs in `MetaM`, so whoever runs it
  supplies this environment, and this reader imports none of it. Every program of this module that
  runs in `MetaM` begins with the library's guard (`LeanIntent.asking`, in
  `LeanIntent/Loaded.lean`), and so do the programs of the other readers it calls: in an
  environment whose extensions' state is not loaded it throws before it asks anything. That state
  is loaded where Lean's elaboration of a file supplies the environment (`Lean/Elab/Import.lean`
  159), and where a compiled gate imports as `docs/confirmation.md` says, which
  `LeanIntent.Imported.loaded` does.
* **What the build stored of each executable**, which the reader imports itself, with no
  extension's state loaded and no code of the executable's modules run: an executable's
  `initialize` declarations are its own start-up, not this check's to run. The reader holds it only
  as a `LeanIntent.Imported.Stored`, whose four questions are all it can ask, and whose module
  comment states, for each, what it reads and where Lean builds it. None is answered from a state
  that loading would change: three read the constants and the modules' headers, and the fourth,
  the stored IR, reads the entries the modules stored, as the next section says. The reader holds
  no `Environment` of that import, so it has none to give a function that reads another state.

## The IR the build stored

The reading relies on these facts about Lean v4.35.0, read from its source:

* `IR.findEnvDecl` (`Lean/Compiler/IR/CompilerM.lean` 142-143) looks a declaration up by its module
  index, in that module's IR entries first and then in its `.olean` entries
  (`Lean/Compiler/LCNF/Basic.lean` 1252-1262), and last in the extension's own state. In an
  environment `importModules` makes, that state is the empty map whether or not the import loads
  the extensions' state: it starts as what the extension's `addImportedFn` builds from no entries
  and is loaded as what that builds from the modules' (`Lean/EnvExtension.lean` 47-48), which is
  the empty map either way (`CompilerM.lean` 85). So only what the modules stored is found, and
  those entries are set before the import reads its choice of loading (`Lean/Environment.lean`
  2377, 2382 and 2404).
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

public section

namespace LeanIntent.Execution.Read

open Lean Meta LeanIntent.Render LeanIntent.Confirmation.Read LeanIntent.Imported

/-- The name `e` reduces to, through the kernel: `Name.anonymous`, or `Name.str` or `Name.num`
applied to a name and a literal. An error when it reduces to anything else. -/
partial def nameLit (e : Expr) : MetaM Name := asking do
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
def claimOf (decl : Name) : MetaM Claim := asking do
  let t ← readWhnf (← getConstInfo decl).type
  unless t.isAppOfArity ``Runs 2 do
    throwError "the type of {decl} is not `LeanIntent.Runs` applied to a deliverable"
  let args ← ctorArgs (← Confirmation.Read.constOf decl) ``Runs.mk 3
  let executable ← try nameLit args[2]! catch e =>
    throwError "the executable {decl} names is not read as a name: {e.toMessageData}"
  return ⟨decl, Implementation.Read.constOf? t.appArg!, executable⟩

/-- The values of `Runs d` the modules `mods` declare, as the build shows them. -/
def claims (mods : Array Name) : MetaM (Array Claim) := asking do
  (← declaredIn mods ``Runs).mapM claimOf

/-- The declarations the IR expression `e` calls (`IR.Expr.fap`) or makes a closure of
(`IR.Expr.pap`). -/
@[expose] def exprRefs : IR.Expr → List Name
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

/-- The declarations that the IR the build stored for `n`, as Lean finds it (`Stored.irDecl?`,
which is `IR.findEnvDecl`), calls or makes a closure of: none where Lean finds no IR for `n`, or
where its IR declares it implemented in another language (`extern`). -/
@[expose] def irRefs (s : Stored) (n : Name) : List Name :=
  match s.irDecl? n with
  | some (.fdecl _ _ _ body _) => bodyRefs body
  | some (.extern ..) | none => []

/-- The modules of `s` whose imports reach the module `m`, `m` included: those whose code can
call a declaration of `m`. -/
@[expose] def importersOf (s : Stored) (m : Name) : Std.HashSet Name := Id.run do
  let mut importers : Std.HashMap Name (Array Name) := {}
  for (n, imports) in s.modules do
    for imp in imports do
      importers := importers.insert imp ((importers.getD imp #[]).push n)
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

/-- **Whether `main` reaches the implementation `c`** in what the build stored of an executable's
modules, `s`, through the declarations each one's stored IR calls or makes a closure of (`irRefs`),
followed only through declarations of modules whose imports reach `c`'s (`importersOf`), since no
other can call it. The declarations are found by a walk from `main` that records what each one's IR
calls, and `c` too for each other declaration with stored IR that is `c`'s compiled code
(`isCompiledCodeOf`, over the constants `s` holds: a reduce-arity copy of `c`), and the verdict is
`Execution.reach` over that record. A declaration's module is the one `s` gives it
(`Stored.moduleOf`). An error when more declarations are reached than `2 ^ 64`. -/
@[expose] def reachesIn (s : Stored) (c : Implementation.Constant) : Except String Bool := do
  unless s.moduleOf c.name == some c.module do return false
  let up := importersOf s c.module
  let code (n : Name) : List Name :=
    if n != c.name && isCompiledCodeOf s.contains c.name n && (s.irDecl? n).isSome
    then [c.name] else []
  let mut table : Std.HashMap Name (List Name) := {}
  let mut work := [`main]
  repeat
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      unless table.contains n do
        let refs := if (s.moduleOf n).any up.contains then irRefs s n ++ code n else []
        table := table.insert n refs
        work := refs ++ work
  match reach (fun n => table.getD n []) `main c.name (2 ^ 64) with
  | .reached => return true
  | .unreached => return false
  | .exhausted => throw "`main` reaches more than 2 ^ 64 declarations"

/-- What the build shows of the executable `name`, whose root module is `root`, in what the build
stored of that module and what it imports, `s`: whether they declare `main`, and which of the
implementations `targets` it reaches. -/
@[expose] def executableIn (s : Stored) (name root : Name) (targets : List Implementation.Constant) :
    Except String Executable := do
  let entry := s.contains `main
  let reached ← if entry then targets.filterM (reachesIn s) else pure []
  return ⟨name, root, entry, reached⟩

/-- **What a gate reads**, from the finished build: the report on what the executables `exes`,
each given by its name and root module as the project's Lake configuration declares them, run of
the project whose modules are `mods`. It reads the deliverables and claims of those modules, the
implementations `Implementation.Read.check` reads of them, and, for each executable, what the
build stored of its root module and what that imports (`Imported.stored`), in which it reads `main`
and what `main` reaches. Its findings are empty exactly when every claim holds
(`Execution.findings_eq_nil_iff`). -/
def check (mods : Array Name) (exes : Array (Name × Name)) : MetaM Report := asking do
  let ds ← declaredIn mods ``Deliverable
  let implemented ← Implementation.Read.check mods
  let is := implemented.implementations.map fun (d, _, c) => (d, c)
  let as := implemented.awaiting.map (·.1)
  let cls ← claims mods
  let es ← exes.mapM fun (name, root) => do
    let targets := (cls.toList.filter (·.executable == name)).flatMap fun cl =>
      is.filterMap fun (d, c) => if cl.deliverable == some d then some c else none
    try
      match executableIn (← stored root (← getOptions)) name root targets.eraseDups with
      | .ok e => return e
      | .error why => throwError "{why}"
    catch err =>
      throwError "the executable {name}, whose root module is {root}, cannot be read: \
        {err.toMessageData}"
  return report ds.toList is as es.toList cls.toList

end LeanIntent.Execution.Read
