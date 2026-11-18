module

import Lean
import Lake
import Lake.Load.Package
meta import Lake
meta import Lake.Load.Package

/-!
# `check`: the repository's checks, and the listing of its tests

Run from the repository's top level as

    lean --run tools/check.lean            # the checks below
    lean --run tools/check.lean --tests    # the listing of tests, for no-mistakes

where `lean` is elan's, which runs the Lean that `lean-toolchain` names. It is not run through
`lake env`, so that it reads the project's configuration before Lake loads it. It is a `module`
file, as its own rule `LEAN-MODULE` requires of every Lean file: `main` is public, and Lake's
modules are imported a second time with `meta`, since Lean loads the compiled code of an imported
module, which `lean --run` runs, only where the import says `meta`. The checks exit with status `0`
when every rule holds and `1` when a rule rejects the project, after printing each rejection to
standard output. When they cannot run they end through an uncaught error, which Lean prints to
standard error and also ends with status `1`. Every input is read through the system that owns it,
never by reading source text by hand:

* the project's Lean files, from Git's index (`git ls-files`); the library's are every one of them
  outside `tools/`, which holds this program;
* the project's configuration, from Lake's own TOML parser (`Lake.Toml.loadToml`) and loader
  (`Lake.loadPackage`, which resolves no dependency);
* the modules each library target selects, from Lake (`Lake.LeanLib.getModuleArray`, which reads
  the target's globs over the working tree, as a build of the target does);
* each file's module name, from Lean (`moduleNameOfFileName`), whether it is a `module` file, from
  Lean's parser of its header (`Parser.parseHeader`), and its build, from Lake;
* the axioms each declaration rests on, from Lean (`collectAxioms`) over the environment Lean
  imports from the built modules, with the state of its environment extensions loaded;
* the compiled code of each declaration and what it uses, from Lean (`Lean.IR.findEnvDecl`,
  `Lean.IR.collectUsedDecls`) over that environment;
* what each declaration names and how it applies it, from Lean: for a library module, the type and
  the value of each constant it declares in that environment, a theorem's proof and an opaque
  constant's value included; for a file under `tools/`, the same of the environment Lean's
  frontend makes of the file, which elaborates it in a process of its own (`--loads`) against the
  built library;
* the attestations of declared types' codes that the library's declarations depend on, from the
  library's own audit (`LeanIntent.CodeAudit.audit`) over the environment Lean imports from the
  built modules, run by `tools/codes.lean` in a process of its own, since this program is not
  built against the library.

The rules:

* `LAKE-CONFIG`: `lakefile.toml` sets only `name`, `defaultTargets`, `leanOptions` (with only
  `autoImplicit` and `relaxedAutoImplicit`) and `lean_lib` tables (with only `name`, `roots` and
  `globs`), and no `lakefile.lean` exists. So the package requires no other package and depends on
  nothing beyond Lean's own libraries, and Lake runs no code of the project to configure it.
* `LEAN-BUILD`: the modules the library targets select are exactly the modules of the library's
  files, and each target selects at least one; and `lake build --wfail` builds every library file,
  given as its target, with no error and no warning. So a build of the library targets builds
  exactly the files these rules build and audit: a library file that no target selects, such as one
  outside the targets' directories, and a module a target selects that Git's index does not list,
  such as a file not yet added, are each refused. Lake rejects a file that is not a module of the
  workspace as an unknown target, and a `sorry` is a warning.
* `LEAN-MODULE`: every Lean file Git's index lists, the library's and those under `tools/`, is a
  `module` file, as Lean's parser reads its header (`Parser.parseHeader`,
  `Elab.HeaderSyntax.isModule`). Lean refuses a `module` file's import of a file that is not one, so
  a project's `module` file can import a module of the library only if the library's file is one.
* `AXIOMS`: no library module declares an axiom, and every constant a library module declares rests
  only on `propext`, `Classical.choice` and `Quot.sound`, Lean's own axioms. So no claim the
  library makes about itself rests on `sorry` (`sorryAx`), on code run to decide it (the axiom
  `native_decide` adds to the module that uses it, asserting what that code returned) or on an
  axiom of the project. The library's modules must declare at least one constant.
* `PROCESS`: the compiled code of the library, each compiled declaration of a library module with
  everything it uses, as Lean's C emitter collects that (`Lean.IR.collectUsedDecls`, closures and
  initializers included), calls no function of Lean's runtime that starts a process or that tells a
  process where it lies or what it runs in (`processQueries`). So a text the library computes takes
  nothing from those, and a checker that refuses a process start can call the library. The one
  exception is `notFollowed`. The rule fails rather than passing when it reads no compiled code,
  when a declaration it reaches has no compiled code to read, or when a function of `boundQueries`
  is not bound to the C function it lists, as a new Lean release might make it. It sees calls by
  name: it does not see a closure called through a value held in a reference, such as Lean's table
  of elaborators, or code of a project that a text's term elaborates.
* `CODES`: the audit of declared types' codes (`LeanIntent.CodeAudit`) accepts every constant the
  library's modules declare, its worked examples included: no declaration they depend on attests a
  declared type's code with a code or isomorphism other than the one the deriving handler writes
  from the type's declaration, and none rests on an axiom other than Lean's three. `tools/codes.lean`
  says what it prints and when it fails; the rule fails rather than passing when the library's
  modules declare no constant.
* `LOADED`: no declaration of a library module, or of a Lean file under `tools/`, imports modules
  in a way that leaves the state of Lean's environment extensions unloaded. A declaration that
  names `importModules` or `finalizeImport` (`importFunctions`), in its type or its value, must
  apply it to `true`, written as that constant, for its parameter `loadExts`; and none may name
  `withImportModules`, which always leaves the state unloaded. Lean's plain import gives every
  extension its initial value as its state and reports nothing (`Lean/Environment.lean` 2428-2432
  at Lean v4.35.0), so a reader's question to Lean, such as whether a declaration is a class
  instance, is then answered from an empty table: the audit of declared types' codes named no
  instance in any refusal that way. Lean itself refuses `loadExts := true` where
  `enableInitializersExecution` was not called first (`Lean/Compiler/InitAttr.lean` 199-201). The
  one exception is `storedImport`, the library's `LeanIntent.Imported.stored`, which hands back no
  environment. The rule fails rather than passing when the pinned Lean's functions are not as it
  expects them or another declaration Lean's modules bring takes a parameter named `loadExts`
  (`importChoices`), when it sees no declaration under `tools/` that imports modules, though this
  program does, and when the library holds no `storedImport` that imports. It sees a function
  named in a declaration's term: it does not see an import made through another function of
  Lean's or Lake's that itself imports with the state unloaded, or by a name given to Lean's
  evaluator.
* `READERS`: every declaration of a library module that is handed an environment refuses one in
  which the state of Lean's environment extensions is not loaded, or is excepted by name as asking
  nothing of that state. A declaration is handed an environment when its type holds one
  (`holdsEnv`): it names Lean's `Environment`, a structure with one inside, or a monad that carries
  one, as `CoreM`, `MetaM` and those built on them do. A project's own gate that imports with
  Lean's default would otherwise hand a reader of the library an environment whose tables are as
  they start, and the reader would compute a text or a verdict from them with no error. Such a
  declaration, where a file writes it, must begin with the library's guard, `LeanIntent.asking` or
  `LeanIntent.askingIn`, which throws before anything is asked; or take a proof of
  `LeanIntent.Loaded`; or be one of `stateless`, whose module's comment shows from Lean's source
  that what it asks is answered by the constants and the modules' headers alone (`readerFault`
  says how each form is read, a recursive definition's included). The rule fails rather than
  passing when it finds no such declaration, and when the library does not declare one it excepts.
  It reads how a declaration begins, not everything it does: a program that began with the guard
  and then ran a question in another environment of its own making would pass, and `LOADED` is the
  rule for that.

The rules read what the build produced, so they hold only if no code the build runs was written to
defeat them: elaborating a Lean file runs the metaprograms it invokes. The same holds of the
`initialize` declarations of the library's modules: this program and `tools/codes.lean` import
those modules with their extensions' state loaded, which runs those declarations in the importing
process (`LeanIntent/Imported.lean` says what that admits), where one could end the process with
the status of a pass.

## The environments this program reads, and what each question reads

Every environment this program holds was imported with the state of Lean's environment extensions
loaded, which `LOADED` checks of its own declarations too. Lean runs `finalizePersistentExtensions`
then (`Lean/Environment.lean` 2404-2405 and 1976-2007), which sets the state of every persistent
extension registered in the process to what the extension builds from the entries the modules
stored, and runs the modules' `initialize` declarations on the way (`LeanIntent/Imported.lean`
gives the order and what running them admits).

| Question | The extension state that answers it | What loads it |
|---|---|---|
| the constants of the library's modules, their modules, types and values (`AXIOMS`, `PROCESS`, `LOADED`, `READERS`) | none: the constant map and the modules' headers | every import builds them (`Environment.lean` 2333-2348 and 2363-2373) |
| the axioms a constant rests on (`AXIOMS`: `collectAxioms`) | the state of the extension in which Lean records each declaration's axioms when it exports a module (`Lean/Util/CollectAxioms.lean` 120-124, read at 149-154); for a constant with no record there, the constants' bodies | this program's import of the library's modules, `importModules` given `loadExts := true` after `enableInitializersExecution` (`check`). With that state unloaded `collectAxioms` found no record and followed every body instead, which is how this rule read before |
| a declaration's compiled code and what it uses (`PROCESS`: `IR.findEnvDecl`, `IR.collectUsedDecls`) | the entries each module stored for the extension of compiled code (`Lean/Compiler/LCNF/Basic.lean` 1252-1261) and for the `init` attributes (`Lean/Compiler/InitAttr.lean` 112-125, through `Lean/Attributes.lean` 306-318); then the states of those extensions, which hold only what the current module adds, loaded or not (`Lean/Compiler/IR/CompilerM.lean` 83-85, `Attributes.lean` 269-270), and an import has no current module | `setImportedEntries` (`Environment.lean` 2377 and 2382), in every import |
| whether a file writes a declaration (`READERS`: `written`) | the entries each module stored for the extension of declaration ranges (`Lean/DeclarationRange.lean` 20-23, read through `MapDeclarationExtension.find?`, `Lean/EnvExtension.lean` 163-170) | `setImportedEntries`, in every import, at the private level, where a module stores them |
| a file's commands, their elaborators and its declarations (`--tests-module`, `--loads`) | whichever states Lean's frontend consults as it elaborates the file | Lean's frontend (`elaborate`: `Elab.processHeader`, `Lean/Elab/Import.lean` 159) |

## The listing of tests

With `--tests` this program checks nothing and prints the tests of the repository, one line each,
for the no-mistakes pipeline, whose `test.tests_as_evidence` setting in `.no-mistakes.yaml` blocks
a change whose listing gains a line that its base's listing lacks. A test is code whose verdict
comes from running it on chosen inputs, rather than from a proof or a type-check over every input.
It reads one Lake project, the one at the repository's top level, and runs only under the Lean
this repository pins (`testsLean`). It reads:

* the project's Lean files, every one Git's index lists, `tools/` included, in an order in which
  every file comes after the files of the project it imports, as Lean's parser reads its header
  (`Parser.parseHeader`);
* each file's commands, from Lean's frontend, which elaborates the file in a process of its own
  (`--tests-module`) against the modules of the project it imports, written by the processes before
  it to a directory removed afterwards, with `debug.byAsSorry`, so that no proof written with `by`
  is elaborated: the syntax of each command as Lean's parser read it, as macros expanded it and as
  Lean elaborated it as a command, and the elaborators that ran, from the info tree of the snapshot
  Lean's frontend makes of the command;
* the test driver `lakefile.toml` names for `lake test`, from Lake's loader.

A command is a test when its syntax holds a token of `testTokens`, the commands, terms and tactics
of the pinned Lean that evaluate code the file writes or compare what running a command, a tactic
or a simp set on a chosen input produced with what the file states; when it holds a configuration
that makes `decide` run compiled code (`nativeConfig`); or when an elaborator the project declares,
other than a macro, elaborates some of it. A test driver is a test too. Each line is the file's
path, quoted; the number of commands of the file, up to and including the test, whose syntax is the
same as its own; and that syntax with positions, whitespace and comments left out (`syntaxKey`). A
line therefore changes only when its test changes, the file is renamed, or a command with the same
syntax is added or removed before it in the file. The listing exits with status `0` and prints
nothing but these lines when it has read every file. It fails, with another status, when Git's
index lists no Lean file, when the imports form a cycle, when Lean cannot elaborate a file or its
imports, when a command holds a token that starts with `#` and a letter that neither `testTokens`
nor `otherTokens` classifies, or when the Lean that runs it is not the release `testsLean` names.

Not every check of a chosen input is listed. A declaration that Lean's elaborator and kernel check,
`theorem` and `example` among them, is not a test unless it holds one of the tokens or
configurations above; a proof about a chosen input, such as `example : f 3 = 9 := by decide`, is
left to review. A proof written with `by` is read only as its syntax, so code that a project's macro
or elaborator, or a configuration given as a term, would run inside it is not seen; nor is code
that Lean evaluates to another end than a verdict, such as `include_str`'s path or a
configuration's value; nor is code that a deriving handler the project declares runs, since a
deriving handler is no elaborator and the commands it elaborates are elaborated by Lean's own, so a
command whose `deriving` clause names one is not listed (the library's handler,
`LeanIntent.Declared`, writes a code and an isomorphism whose proofs Lean's kernel checks).
-/

open Lean

namespace Check

/-- A rejection: the code of the rule that rejects and what it rejects. -/
structure Rejection where
  rule : String
  message : String

/-- Lean's own axioms, the only ones a library declaration may rest on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Runs `cmd` with `args`, returning its exit status and its standard output and error. -/
def run (cmd : String) (args : Array String) : IO (UInt32 × String) := do
  let out ← IO.Process.output { cmd, args }
  return (out.exitCode, out.stdout ++ out.stderr)

/-- The output of `git` run with `args`, or an error when it fails. -/
def git (args : Array String) : IO String := do
  let o ← IO.Process.output { cmd := "git", args }
  unless o.exitCode == 0 do
    throw <| IO.userError s!"git {" ".intercalate args.toList} failed:\n{o.stderr}"
  return o.stdout

/-- The Lean files that Git's index lists under the current directory, relative to it. -/
def trackedLeanFiles : IO (Array String) := do
  let out ← git #["ls-files", "-z", "--", "*.lean"]
  return ((out.splitOn "\x00").filter (· ≠ "")).toArray

/-- The library's Lean files: the tracked Lean files outside `tools/`. -/
def libraryFiles : IO (Array String) :=
  return (← trackedLeanFiles).filter (!·.startsWith "tools/")

/-- The module names Lean gives the files of `files`, relative to the current directory. -/
def moduleNames (files : Array String) : IO (Array Name) := do
  let cwd ← IO.currentDir
  files.mapM fun f => moduleNameOfFileName (System.FilePath.mk f) (some cwd)

/-- The configuration of the project in the current directory, as Lake's own loader reads it from
`lakefile.toml`, without resolving dependencies, so that reading it runs no code of the project. -/
def loadConfig : IO Lake.Package := do
  let (elan?, lean?, lake?) ← Lake.findInstall?
  let some lean := lean? | throw <| IO.userError "Lake found no Lean installation"
  let some lake := lake? | throw <| IO.userError "Lake found no Lake installation"
  let lakeEnv ← match ← (Lake.Env.compute lake lean elan?).toBaseIO with
    | .ok env => pure env
    | .error e => throw <| IO.userError e
  let wsDir ← IO.currentDir
  let some pkg ← (Lake.loadPackage
      { lakeEnv, wsDir, relConfigFile := "lakefile.toml", configLang? := some .toml }).toBaseIO
    | throw <| IO.userError "Lake could not load lakefile.toml"
  return pkg

/-- The keys of the table `t` that `allowed` does not hold, each written after `path`. -/
def extraKeys (path : String) (allowed : List Name) (t : Lake.Toml.Table) : Array String :=
  t.items.filterMap fun (k, _) => if allowed.contains k then none else some s!"{path}{k}"

/-- The keys of `lakefile.toml`, as Lake's own TOML parser reads it into `t`, that `LAKE-CONFIG`
does not allow; a value of another shape than an allowed key takes counts as a key not allowed. -/
def configExtraKeys (t : Lake.Toml.Table) : Array String := Id.run do
  let mut extra := extraKeys "" [`name, `defaultTargets, `leanOptions, `lean_lib] t
  for (k, v) in t.items do
    if k == `leanOptions then
      match v with
      | .table _ o => extra := extra ++ extraKeys "leanOptions." [`autoImplicit, `relaxedAutoImplicit] o
      | _ => extra := extra.push "leanOptions, which is not a table"
    else if k == `lean_lib then
      match v with
      | .array _ vs =>
        for target in vs do
          match target with
          | .table _ t => extra := extra ++ extraKeys "lean_lib." [`name, `roots, `globs] t
          | _ => extra := extra.push "lean_lib, an entry of which is not a table"
      | _ => extra := extra.push "lean_lib, which is not an array of tables"
  return extra

/-- `LAKE-CONFIG` for the project in the current directory. -/
def checkConfig : IO (Array Rejection) := do
  let reject (message : String) : Rejection := { rule := "LAKE-CONFIG", message }
  let mut errs : Array Rejection := #[]
  if ← System.FilePath.pathExists "lakefile.lean" then
    errs := errs.push (reject "lakefile.lean exists, and Lake would configure the project by running it instead of reading lakefile.toml")
  let input ← IO.FS.readFile "lakefile.toml"
  let table ← match ← (Lake.Toml.loadToml (Parser.mkInputContext input "lakefile.toml")).toBaseIO with
    | .ok t => pure t
    | .error log => throw <| IO.userError s!"Lake's TOML parser could not read lakefile.toml:\n{← log.toList.mapM (·.toString)}"
  for k in configExtraKeys table do
    errs := errs.push (reject s!"lakefile.toml sets {k}, which is not among the keys this rule allows")
  return errs

/-- `LEAN-BUILD`'s first part: the modules the library targets of `pkg` select, as Lake reads each
target's globs over the working tree, are exactly `mods`, the modules Lean gives the library files
`files`, and each target selects at least one. -/
def checkModules (pkg : Lake.Package) (files : Array String) (mods : Array Name) :
    IO (Array Rejection) := do
  let reject (message : String) : Rejection := { rule := "LEAN-BUILD", message }
  let mut errs : Array Rejection := #[]
  let mut selected : Array Name := #[]
  for lib in pkg.leanLibs do
    let libMods := (← lib.getModuleArray).map (·.name)
    if libMods.isEmpty then
      errs := errs.push (reject s!"the library target {lib.name} selects no module")
    selected := selected ++ libMods
  for (f, m) in files.zip mods do
    unless selected.contains m do
      errs := errs.push (reject s!"{f}, a library file Git's index lists, is the module {m}, which no library target selects, so a build of the targets does not build it")
  for m in selected do
    unless mods.contains m do
      errs := errs.push (reject s!"a library target selects the module {m}, whose file Git's index does not list, so these rules do not build or audit it")
  return errs

/-- `LEAN-MODULE` for the Lean files `files`: each is a `module` file, as Lean's parser reads its
header. A file whose header Lean's parser cannot read is an error, since the rule cannot decide it. -/
def checkModuleFiles (files : Array String) : IO (Array Rejection) := do
  let mut errs : Array Rejection := #[]
  for f in files do
    let input ← IO.FS.readFile f
    let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext input f)
    if messages.hasErrors then
      throw <| IO.userError s!"{f}: Lean's parser could not read its header"
    unless Elab.HeaderSyntax.isModule header do
      errs := errs.push { rule := "LEAN-MODULE", message :=
        s!"{f} is not a `module` file: its header does not begin with `module`" }
  return errs

/-- `LEAN-BUILD`'s second part: Lake builds every file of `files`, each given as its target, with
warnings as errors. -/
def build (files : Array String) : IO (Array Rejection) := do
  let (code, out) ← run "lake" (#["build", "--wfail"] ++ files)
  if code == 0 then
    return #[]
  return #[{ rule := "LEAN-BUILD", message :=
    s!"lake build --wfail of the library's Lean files failed; a file that is not a module of the workspace is an unknown target:\n{out}" }]

/-- `CODES` for the library's modules `mods`, built into the directory `libDir`, by the status of
`tools/codes.lean`: no rejection for `0`; for `1`, a refusal, one rejection for each line it printed
to standard output, or, when it printed none, one rejection carrying its standard error; and for
any other status, `2` when it could not run, an error carrying its standard output and error. -/
def checkCodes (libDir : System.FilePath) (mods : Array Name) : IO (Array Rejection) := do
  let args := #["--run", "tools/codes.lean"] ++ mods.map (·.toString)
  let o ← IO.Process.output { cmd := "lean", args, env := #[("LEAN_PATH", some libDir.toString)] }
  match o.exitCode with
  | 0 => return #[]
  | 1 =>
    let lines := ((o.stdout.splitOn "\n").filter (· ≠ "")).toArray
    if lines.isEmpty then
      return #[{ rule := "CODES", message :=
        s!"tools/codes.lean exited with status 1 and printed no reason; its standard error:\n{o.stderr}" }]
    return lines.map fun l => { rule := "CODES", message := l }
  | c => throw <| IO.userError s!"tools/codes.lean could not run (status {c}):\n{o.stdout}{o.stderr}"

/-- The axioms that the constant `c` of `env` rests on, as Lean collects them. -/
def axiomsOf (env : Environment) (c : Name) : IO (Array Name) :=
  (collectAxioms c : CoreM (Array Name)).toIO' { fileName := "<check>", fileMap := default } { env }

/-- `AXIOMS` for the constant `c`, declared by the module `mod`. -/
def auditConstant (env : Environment) (mod : Name) (c : Name) (ci : ConstantInfo) :
    IO (Array Rejection) := do
  let mut errs : Array Rejection := #[]
  let reject (what : String) : Rejection := { rule := "AXIOMS", message := s!"{mod}: {c} {what}" }
  if ci matches .axiomInfo _ then
    errs := errs.push (reject "is an axiom declared by a library module")
  for a in ← axiomsOf env c do
    unless allowedAxioms.contains a do
      errs := errs.push (reject s!"rests on the axiom {a}")
  return errs

/-- The atoms of `stx`, appended to `acc`. -/
partial def atoms (stx : Syntax) (acc : Array String) : Array String :=
  match stx with
  | .atom _ val => acc.push val
  | .node _ _ args => args.foldl (fun acc arg => atoms arg acc) acc
  | _ => acc

/-- The nodes of `stx`, appended to `acc`. -/
partial def nodes (stx : Syntax) (acc : Array Syntax) : Array Syntax :=
  match stx with
  | .node _ _ args => args.foldl (fun acc arg => nodes arg acc) (acc.push stx)
  | _ => acc


/-- The Lean release whose elaborators `testTokens`, `otherTokens` and `nativeConfig` describe. They
were read from Lean 4.34.1 and again from 4.35.0: 4.35.0's token table, with `Lean`, `Lake` and
`Std` imported, holds the same 29 tokens that start with `#` and a letter as 4.34.1's; and the
declarations of its modules under `Lean.Elab`, `Lean.Meta`, `Std` and `Lake` that use
`evalTerm`, `evalExpr`, `evalConst` or `Meta.nativeEqTrue` differ from 4.34.1's only by one
declaration moved to another module, by the configuration of the `constructor` tactic, which Lean
evaluates to its value, and by the removal of `Meta.reduceBoolNative`, which served
`Lean.reduceBool`, a constant 4.35.0 no longer has. The listing refuses to run under any other
release, whose elaborators they may not describe. -/
def testsLean : String := "4.35.0"

/-- The tokens of the commands, terms and tactics of the pinned Lean whose verdict comes from
running code on inputs the file chooses, rather than from Lean's elaborator and kernel checking
that a term has a type. Two kinds, read from the pinned Lean's elaborators:

* those that evaluate a term the file writes with Lean's evaluator (`evalTerm`, `evalExpr`,
  `evalConst`) and fail when the evaluation throws or yields `false`: `#eval`, `#eval!` and `#guard`;
  `run_cmd`, `run_elab`, `run_meta` and `run_tac`, which run a metaprogram, and `by_elab`, which runs
  one to make a term; `test_extern`, which compares a function's compiled implementation with its
  definition on an input; and `native_decide`, which takes its decision from compiled code
  (`Meta.nativeEqTrue`) and adds an axiom asserting it, instead of Lean's kernel reducing it;
* those that run a command, a tactic or a simp set on an input the file chooses and compare what it
  produced with what the file states: `#guard_msgs`, `#guard_panic`, `#guard_expr`, `#check_simp`,
  `#check_tactic` and `#check_tactic_failure`.

The evaluating elaborators were found by searching the pinned Lean for calls of its evaluators and
of `Meta.nativeEqTrue`. Those that evaluate code the file writes to another end than a verdict on
it are not tests: `include_str` evaluates the path of a file it includes, `#widget` the widget it
displays and a tactic's configuration its value, and `idbg` is a debugger; `dbg_trace` runs only
when compiled code runs. Code written to fail on a chosen input there is not listed. `bv_decide` and
`bv_check` call `Meta.nativeEqTrue` on Lean's own checker of a certificate, not on code the file
writes, and prove their goal for every value of its variables; `AXIOMS` refuses the axiom they add.
The commands of the second kind are the tokens of the pinned Lean's token table, with `Lean`,
`Lake` and `Std` imported, that start with `#` and a letter, each read from its elaborator. -/
def testTokens : List String :=
  ["#eval", "#eval!", "#guard", "run_cmd", "run_elab", "run_meta", "run_tac", "by_elab",
   "test_extern", "native_decide", "#guard_msgs", "#guard_panic", "#guard_expr", "#check_simp",
   "#check_tactic", "#check_tactic_failure"]

/-- The rest of those tokens of the pinned Lean that start with `#` and a letter, none of which is a
test: the command fails only when Lean cannot elaborate what it is given, so its verdict is a
type-check (`#check`, `#check_failure`, which succeeds only when its term does not type-check,
`#synth`, `#reduce`), or it prints or reports what Lean has (`#print`, `#where`, `#version`, ...,
and `#grind_lint`, which reports how many theorems `grind` instantiates), or it runs the command
it is given (`#time`, `#info_trees`, `#with_exporting`), or it evaluates the widget it displays
(`#widget`), or it is the vector literal `#v[`. A token that starts with `#` and a letter and is in
neither set makes the listing an error, so that no such command goes unclassified. -/
def otherTokens : List String :=
  ["#check", "#check_failure", "#check_assertions", "#synth", "#reduce", "#print", "#where",
   "#version", "#exit", "#import_path", "#show_deprecated_modules", "#dump_async_env_state",
   "#discr_tree_key", "#discr_tree_simp_key", "#grind_lint", "#widget", "#time", "#info_trees",
   "#with_exporting", "#v["]

/-- Whether `n` is syntax that makes `decide` take its decision from compiled code
(`Meta.nativeEqTrue`): a configuration item that sets `native`, `+native` or `(native := v)`, or a
`decide` whose configuration holds `(config := c)`, whose value Lean evaluates into the whole
configuration of `decide`, `native` included. -/
def nativeConfig (n : Syntax) : Bool :=
  let item (kinds : List Name) (names : List Name) (m : Syntax) : Bool :=
    kinds.contains m.getKind && m[1].isIdent && names.contains m[1].getId
  let vals := [``Parser.Term.valConfigItem, ``Parser.Tactic.valConfigItem]
  item ([``Parser.Term.posConfigItem, ``Parser.Tactic.posConfigItem] ++ vals) [`native] n ||
    (n.getKind == ``Parser.Tactic.decide && (nodes n #[]).any (item vals [`config]))

/-- `n` written so that distinct names give distinct strings: each component in turn, a string as a
quoted literal and a number in decimal, after `_` for the anonymous name. -/
def nameKey : Name → String
  | .anonymous => "_"
  | .str p s => nameKey p ++ "." ++ s.quote
  | .num p k => nameKey p ++ "." ++ toString k

/-- `stx` with its source information left out (positions, whitespace and comments, which Lean's
parser keeps there as trivia): a node as its kind and its children in parentheses, an atom as its
quoted text and an identifier as its name, so that two syntax trees give the same string exactly
when they agree in kinds, atoms, names and shape. -/
partial def syntaxKey : Syntax → String
  | .missing => "?"
  | .atom _ val => val.quote
  | .ident _ _ n _ => "`" ++ nameKey n
  | .node _ k args => "(" ++ nameKey k ++ args.foldl (fun acc a => acc ++ " " ++ syntaxKey a) "" ++ ")"

/-- `file`, the module `mod`, as Lean's frontend elaborates it under `opts`, with the info tree of
each command kept: its state once every command is elaborated, whose environment holds what the
file declares. The frontend imports the modules the file's header names with every environment
extension's state loaded (`Elab.processHeader`, which gives `importModules` `loadExts := true`,
`Lean/Elab/Import.lean` 159 at Lean v4.35.0), which Lean allows only after
`enableInitializersExecution`, so what this program asks of that environment afterwards is answered
as it is while Lean elaborates the file. An error naming `path` and saying `so`, with Lean's
messages, when Lean cannot elaborate the file or its imports. -/
unsafe def elaborate (path file : String) (mod : Name) (opts : Options) (so : String) :
    IO Elab.IncrementalState := do
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let fail (messages : MessageLog) : IO Elab.IncrementalState := do
    let shown ← messages.toList.mapM (·.toString)
    throw <| IO.userError s!"{path}: Lean could not elaborate it, {so}:\n{String.join shown}"
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  enableInitializersExecution
  let (env, messages) ← Elab.processHeader header opts messages inputCtx (mainModule := mod)
  if messages.hasErrors then
    return ← fail messages
  let state := Elab.Command.mkState env messages opts
  let state := { state with infoState := { state.infoState with enabled := true } }
  let s ← Elab.IO.processCommandsIncrementally inputCtx parserState state none
  if s.commandState.messages.hasErrors then
    return ← fail s.commandState.messages
  return s

/-- The tests of `file`, the module `mod` of a project whose modules are `mods`, read by Lean's
frontend as it elaborates the file with `debug.byAsSorry`, which elaborates every `by` block whose
type is a proposition as `sorry`. A command is a test when Lean, while it elaborates the command,
runs code on inputs the file chooses and takes the command's verdict from that run: its syntax, as
Lean's parser read it, as a macro expanded it or as Lean elaborated it as a command, holds a token
of `testTokens` or syntax that `nativeConfig` accepts, or some of it is elaborated by an elaborator
the project declares other than a macro. A command's syntax and the info tree of its elaboration
are those of the snapshot Lean's frontend makes of the command, the info tree that records its
macro expansions and elaborators. Each test is printed as the file's path from the repository's top
level, the number of commands of the file before it, the test included, whose syntax is the same
as its own, and `syntaxKey` of its syntax. The module is then written to `out`, so that the modules
that import it can be elaborated. A file Lean cannot elaborate, its imports included, is an error,
and so is a command whose syntax holds a token that starts with `#` and a letter and is in neither
`testTokens` nor `otherTokens`. -/
unsafe def testsOfModule (path file : String) (mod : Name) (mods : Array Name)
    (out : System.FilePath) : IO (Array String) := do
  let opts := (({} : Options).setBool `Elab.async false).setBool `debug.byAsSorry true
  let s ← elaborate path file mod opts "so its tests cannot be read"
  let env := s.commandState.env
  let declared (c : Name) : Bool :=
    match env.getModuleIdxFor? c with
    | some idx => env.header.moduleNames[idx.toNat]?.any mods.contains
    | none => env.contains c
  let isMacro (c : Name) : Bool := (env.find? c).any (·.type.isConstOf ``Macro)
  let mut snap := s.initialSnap
  let mut seen : Std.HashMap String Nat := {}
  let mut tests : Array String := #[]
  repeat
    let cmd := snap.stx
    let key := syntaxKey cmd
    let k := seen.getD key 0 + 1
    seen := seen.insert key k
    let trees := snap.elabSnap.infoTreeSnap.get.infoTree?.toList
    let (syntaxes, elaborators) := trees.foldl (init := (#[cmd], #[]))
      fun acc tree => tree.foldInfo (init := acc) fun _ info (ss, es) =>
        match info with
        | .ofCommandInfo i => (ss.push i.stx, es.push i.elaborator)
        | .ofTermInfo i => (ss, es.push i.elaborator)
        | .ofTacticInfo i => (ss, es.push i.elaborator)
        | .ofMacroExpansionInfo i => (ss.push i.output, es)
        | _ => (ss, es)
    let tokens := syntaxes.foldl (fun acc stx => atoms stx acc) #[]
    for a in tokens do
      if let '#' :: c :: _ := a.toList then
        unless !c.isAlpha || testTokens.contains a || otherTokens.contains a do
          throw <| IO.userError s!"{path}: the command token {a} is neither a test's nor another's that the listing knows"
    if tokens.any testTokens.contains ||
        (syntaxes.foldl (fun acc stx => nodes stx acc) #[]).any nativeConfig ||
        elaborators.any (fun e => declared e && !isMacro e) then
      tests := tests.push s!"{path.quote} {k} {key}"
    match snap.nextCmdSnap? with
    | some next => snap := next.get
    | none => break
  let olean := modToFilePath out mod "olean"
  if let some dir := olean.parent then IO.FS.createDirAll dir
  writeModule env olean
  return tests

/-- The modules `file` imports, as Lean's parser reads its header. -/
def importsOf (file : String) : IO (Array Name) := do
  let input ← IO.FS.readFile file
  let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext input file)
  if messages.hasErrors then
    throw <| IO.userError s!"{file}: Lean's parser could not read its header"
  return (Elab.headerToImports header).map (·.module)

/-- The numbers below `n` in an order in which each comes after every number `deps` gives it, or
`none` when no such order exists because the numbers' `deps` form a cycle. -/
partial def importOrder (n : Nat) (deps : Nat → Array Nat) : Option (Array Nat) :=
  let rec go (done : Array Nat) : Option (Array Nat) :=
    if done.size == n then some done
    else match (List.range n).find? fun i => !done.contains i && (deps i).all done.contains with
      | some i => go (done.push i)
      | none => none
  go #[]

/-- The file in `out` to which `moduleTests` writes the tests of the module `mod`. -/
def moduleTestsFile (out : System.FilePath) (mod : Name) : System.FilePath :=
  modToFilePath out mod "tests"

/-- The lines this program prints when `lean` runs it with `args` in `cwd`, or an error holding its
output when it exits with any status but `0`. -/
def runSelf (args : Array String) (cwd : Option System.FilePath := none) : IO (Array String) := do
  let top := System.FilePath.mk (← git #["rev-parse", "--show-toplevel"]).trimAscii.toString
  let script := top / "tools" / "check.lean"
  let o ← IO.Process.output { cmd := "lean", args := #["--run", script.toString] ++ args, cwd }
  unless o.exitCode == 0 do
    throw <| IO.userError s!"lean --run tools/check.lean {" ".intercalate args.toList} exited with status {o.exitCode}:\n{o.stderr}{o.stdout}"
  return ((o.stdout.splitOn "\n").filter (· ≠ "")).toArray

/-- Writes the tests of `file`, one of the tracked Lean files of the project in the current
directory, whose imports of the project are written to `out` (`testsOfModule`), to the file
`moduleTestsFile` names, read by this program in a process of its own, so that no module's
environment stays in memory while the next is elaborated. -/
unsafe def moduleTests (file out : String) : IO Unit := do
  let files ← trackedLeanFiles
  let mods ← moduleNames files
  let some mod := (files.zip mods).find? (·.1 == file) |>.map (·.2)
    | throw <| IO.userError s!"{file} is not a Lean file Git's index lists here"
  let pre := (← git #["rev-parse", "--show-prefix"]).trimAscii.toString
  initSearchPath (← findSysroot) [out]
  let tests ← testsOfModule (pre ++ file) file mod mods out
  IO.FS.writeFile (moduleTestsFile out mod) (String.join (tests.toList.map (· ++ "\n")))

/-- The tests of the project in the current directory: those `moduleTests` reads in each tracked
Lean file, every file read after the files of the project it imports, whose modules are written to
a directory removed afterwards; and the test driver Lake would run for `lake test`, if
`lakefile.toml` names one, as Lake's loader reads it. Each file's tests are read from the file
`moduleTests` writes, not from what its process prints, which holds whatever the code the project's
commands run prints. -/
def projectTests : IO (Array String) := do
  unless Lean.versionString == testsLean do
    throw <| IO.userError s!"the tests are read for Lean {testsLean}, not Lean {Lean.versionString}, which runs here: read testTokens, otherTokens and nativeConfig again from its elaborators"
  let files ← trackedLeanFiles
  if files.isEmpty then
    throw <| IO.userError "the project tracks no Lean file"
  let mods ← moduleNames files
  let deps ← files.mapM fun f => return (← importsOf f).filterMap fun m => mods.findIdx? (· == m)
  let some order := importOrder files.size (deps[·]!)
    | throw <| IO.userError "the imports of the project's Lean files form a cycle"
  let out ← IO.FS.createTempDir
  try
    let mut tests : Array String := #[]
    for i in order do
      discard <| runSelf #["--tests-module", files[i]!, out.toString]
      tests := tests ++ (← IO.FS.lines (moduleTestsFile out mods[i]!))
    let pkg ← loadConfig
    unless pkg.testDriver.isEmpty do
      let pre := (← git #["rev-parse", "--show-prefix"]).trimAscii.toString
      tests := tests.push s!"{(pre ++ "lakefile.toml").quote} testDriver {pkg.testDriver.quote}"
    return tests
  finally
    IO.FS.removeDirAll out


/-- The declarations of Lean's `Init` that `PROCESS` confirms are bound to the C function it looks
for: the functions of `IO` that start a process (`IO.Process.output` and `IO.Process.run` go through
`IO.Process.spawn`), that say where the process lies or what its environment holds. -/
def boundQueries : List (Name × String) :=
  [(``IO.Process.spawn, "lean_io_process_spawn"), (``IO.appPath, "lean_io_app_path"),
   (``IO.currentDir, "lean_io_current_dir"),
   (``IO.Process.getCurrentDir, "lean_io_process_get_current_dir"),
   (``IO.getEnv, "lean_io_getenv")]

/-- The C functions of Lean's runtime that `PROCESS` refuses: those of `boundQueries`, and libuv's
that say the same or what user and host the process runs as (`Std.Internal.UV.System`, read at Lean
v4.35.0 by a search of every `extern` attribute for names holding `spawn`, `exec`, `fork`, `system`,
`getenv`, `environ`, `app_path`, `exe`, `current_dir`, `cwd`, `homedir`, `tmpdir`, `passwd`,
`hostname` or `uname`). -/
def processQueries : List String :=
  boundQueries.map (·.2) ++
    ["lean_uv_exepath", "lean_uv_cwd", "lean_uv_os_getenv", "lean_uv_os_environ",
     "lean_uv_os_homedir", "lean_uv_os_tmpdir", "lean_uv_os_get_passwd", "lean_uv_os_gethostname",
     "lean_uv_os_uname"]

/-- What `PROCESS` does not follow, each with its reason. `Lean.manualRoot` reads `LEAN_MANUAL_ROOT`
when Lean starts, for the links to Lean's manual it writes into a logged error and a docstring
(`Lean/DocString/Links.lean`, `Lean/Log.lean`), neither of which any text of the library prints. -/
def notFollowed : List Name := [`Lean.manualRoot]

/-- Whether a compiled binding `entry` calls the C function `symbol`. -/
def bindsTo (symbol : String) : ExternEntry → Bool
  | .standard _ fn => fn == symbol
  | .inline _ pattern => (pattern.splitOn symbol).length > 1
  | _ => false

/-- `PROCESS` over the compiled declarations `roots`, reached in the environment `env`. -/
def checkProcess (env : Environment) (roots : Array Name) : Array Rejection := Id.run do
  let reject (message : String) : Rejection := { rule := "PROCESS", message }
  if roots.isEmpty then
    return #[reject "the library's modules hold no compiled code"]
  let mut errs : Array Rejection := #[]
  for (decl, symbol) in boundQueries do
    let bound := match IR.findEnvDecl env decl with
      | some (.extern _ _ _ data) => data.entries.any (bindsTo symbol)
      | _ => false
    unless bound do
      errs := errs.push <| reject s!"{decl} is not bound to {symbol} under this Lean: read processQueries again from its extern attributes"
  -- A breadth-first walk, whose parent map names one way each declaration is reached.
  let mut parent : Std.HashMap Name Name := roots.foldl (fun m r => m.insert r r) {}
  let mut queue := roots
  let mut next := 0
  let path (parent : Std.HashMap Name Name) (c : Name) : List Name := Id.run do
    let mut out := [c]
    let mut at' := c
    for _ in [0:64] do
      let p := parent.getD at' at'
      if p == at' then break
      out := p :: out
      at' := p
    return out
  while h : next < queue.size do
    let c := queue[next]
    next := next + 1
    if notFollowed.contains c then continue
    let some decl := IR.findEnvDecl env c
      | errs := errs.push <| reject s!"{path parent c} reaches a declaration with no compiled code to read"
    if let .extern _ _ _ data := decl then
      if data.entries.any (· matches .opaque) then
        errs := errs.push <| reject s!"{path parent c} reaches a declaration whose compiled code is not exported"
      if let some symbol := processQueries.find? fun s => data.entries.any (bindsTo s) then
        errs := errs.push <| reject s!"{path parent c} calls {symbol}"
    for used in IR.collectUsedDecls env [decl] do
      unless parent.contains used do
        parent := parent.insert used c
        queue := queue.push used
  return errs

/-- The functions of the pinned Lean through which a program chooses whether the environment it
imports has its environment extensions' state loaded: `importModules` and `finalizeImport` take the
choice as a parameter named `loadExts`, and `withImportModules` calls `importModules` with
`loadExts := false` whatever it is given (`Lean/Environment.lean` 2308-2309, 2439-2440 and
2458-2460 at Lean v4.35.0, the only declarations of that file that name `loadExts`). `LOADED`
reads the parameter's position from each function's type and never from this comment. -/
def importFunctions : List Name := [``importModules, ``finalizeImport]

/-- The function of the pinned Lean that imports modules and always leaves the extensions' state
unloaded (`importFunctions`). -/
def unloadedImport : Name := ``withImportModules

/-- The one declaration that `LOADED` lets import without loading the extensions' state: the
library's `LeanIntent.Imported.stored`, which hands back no environment, only the four questions of
a `LeanIntent.Imported.Stored`, none of which an extension's state answers. The rule takes this from
the declaration's name: that it keeps the environment to itself is its own module's statement. -/
def storedImport : Name := `LeanIntent.Imported.stored

/-- The position, among the parameters of a function of type `t`, of the one named `loadExts`. -/
def loadExtsPosition (t : Expr) : Option Nat :=
  go 0 t
where
  go (i : Nat) : Expr → Option Nat
    | .forallE n _ b _ => if n.eraseMacroScopes == `loadExts then some i else go (i + 1) b
    | .mdata _ b => go i b
    | _ => none

/-- What `LOADED` refuses to see named, read from `env`: each function of `importFunctions` with
the position of its parameter `loadExts`, and `unloadedImport` with none. An error, so that the rule
fails rather than passing on a Lean it does not describe, when one of them is not declared, when a
function of `importFunctions` has no parameter of that name, or when another declaration `env`
imports has one, which would be a function carrying the same choice that the rule does not know. -/
def importChoices (env : Environment) : Except String (List (Name × Option Nat)) := do
  let again := "read the rule LOADED again from this Lean's source"
  let mut choices := []
  for f in importFunctions do
    let some ci := env.find? f
      | throw s!"{f} is not declared under this Lean: {again}"
    let some i := loadExtsPosition ci.type
      | throw s!"{f} takes no parameter named loadExts under this Lean: {again}"
    choices := (f, some i) :: choices
  unless env.contains unloadedImport do
    throw s!"{unloadedImport} is not declared under this Lean: {again}"
  let others := env.constants.map₁.fold (init := #[]) fun acc c ci =>
    if !importFunctions.contains c && (loadExtsPosition ci.type).isSome then acc.push c else acc
  unless others.isEmpty do
    throw s!"{others.qsort Name.lt} take a parameter named loadExts under this Lean, and the rule LOADED does not know them: {again}"
  return (unloadedImport, none) :: choices

/-- Why the expression `e` imports modules in a way `LOADED` refuses, appended to `acc`: a reason
for each occurrence of a function of `choices` that is not applied to enough arguments to reach its
parameter `loadExts` with the constant `true` there, and for each occurrence of the function that
has no such parameter. An argument that is not that constant, such as a variable or a term that
reduces to `true`, is refused: the rule accepts the literal and nothing else. -/
partial def importFaults (choices : List (Name × Option Nat)) (e : Expr) (acc : Array String) :
    Array String :=
  let acc := match e.getAppFn with
    | .const c _ =>
      match choices.lookup c with
      | none => acc
      | some none =>
        acc.push s!"names {c}, which leaves every environment extension's state unloaded"
      | some (some i) =>
        if (e.getAppArgs[i]?.map (·.consumeMData.isConstOf ``Bool.true)) == some true then acc
        else acc.push s!"names {c} without `loadExts := true` written as its argument"
    | .lam _ t b _ | .forallE _ t b _ => importFaults choices b (importFaults choices t acc)
    | .letE _ t v b _ =>
      importFaults choices b (importFaults choices v (importFaults choices t acc))
    | .mdata _ b | .proj _ _ b => importFaults choices b acc
    | .app .. | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => acc
  e.getAppArgs.foldl (fun acc a => importFaults choices a acc) acc

/-- `LOADED` for the declaration `ci`: whether its type or its value, a theorem's proof and an
opaque constant's value included, names a function of `choices`, and why the rule refuses it
(`importFaults`), each reason once, nothing when it does not. -/
def loadsOf (choices : List (Name × Option Nat)) (ci : ConstantInfo) : Bool × Array String :=
  let exprs := (ci.type :: (ci.value? (allowOpaque := true)).toList).filter fun e =>
    e.getUsedConstants.any fun c => (choices.lookup c).isSome
  let faults := exprs.foldl (fun acc e => importFaults choices e acc) #[]
  (!exprs.isEmpty, faults.foldl (fun acc f => if acc.contains f then acc else acc.push f) #[])

/-- The library's guards (`LeanIntent/Loaded.lean`): a program that begins with one of them throws,
before it asks anything, in an environment whose extensions' state is not loaded. -/
def guards : List Name := [`LeanIntent.asking, `LeanIntent.askingIn]

/-- The proposition, of the same module, that the state of an environment's extensions is loaded: a
function that takes a proof of it is not given an environment in which it is not. -/
def loadedProof : Name := `LeanIntent.Loaded

/-- The declarations of the library that `READERS` excepts by name. The first four are the test
and the guards themselves, and `LeanIntent.Imported.loaded` makes a loaded environment and is
handed none. Each of the others is handed an environment and asks it only for its constants, the
module of each and the modules' headers and stored entries, which every import builds: the comment
of the module that declares it has a row for each of its questions, with the lines of Lean's source
the row rests on. The rule takes the exception from the name and reads no row. -/
def stateless : List Name :=
  [`LeanIntent.Loaded, `LeanIntent.isLoaded, `LeanIntent.asking, `LeanIntent.askingIn,
   `LeanIntent.Imported.loaded,
   `LeanIntent.Cone.lookupIn, `LeanIntent.Cone.checkRecord, `LeanIntent.Cone.firstUnknown,
   `LeanIntent.CodeAudit.relevantIn, `LeanIntent.CodeAudit.importers,
   `LeanIntent.CodeAudit.generatedBy, `LeanIntent.CodeAudit.instMonadEnvEnvM,
   `LeanIntent.Render.bareConsts, `LeanIntent.Render.recursionKind, `LeanIntent.Render.stopAt]

/-- Whether the type-level constant `c` of `env` holds an environment: it is Lean's `Environment`
or its kernel's, an inductive type one of whose constructors' types names a constant that holds
one, or a definition of a type, such as a monad, whose value names one. The state remembers each
constant's answer, and answers no for a constant being decided, so that a type that mentions
itself ends. -/
partial def holdsEnv (env : Environment) (c : Name) : StateM (Std.HashMap Name Bool) Bool := do
  if c == ``Environment || c == ``Kernel.Environment then return true
  if let some known := (← get)[c]? then return known
  modify (·.insert c false)
  let named : Array Name := match env.find? c with
    | some (.inductInfo v) => v.ctors.foldl (init := #[]) fun acc k =>
        match env.find? k with
        | some ki => acc ++ ki.type.getUsedConstants
        | none => acc
    | some (.defnInfo v) =>
        if v.type.getForallBody.isSort then v.value.getUsedConstants else #[]
    | _ => #[]
  let mut holds := false
  for n in named do
    if ← holdsEnv env n then
      holds := true
      break
  modify (·.insert c holds)
  return holds

/-- Whether `e`, under its leading `fun`s, is an application of one of `guards`. -/
def guardedValue : Expr → Bool
  | .lam _ _ b _ | .mdata _ b => guardedValue b
  | e => match e.getAppFn with
    | .const c _ => guards.contains c
    | _ => false

/-- Whether a function of type `t` takes a proof of `loadedProof` among its parameters. -/
def takesLoaded : Expr → Bool
  | .forallE _ t b _ => t.getAppFn.isConstOf loadedProof || takesLoaded b
  | .mdata _ b => takesLoaded b
  | _ => false

/-- Whether Lean records a place in a source file for the declaration `c` of `env`
(`declRangeExt`, which a module stores at the private level this program imports at): it does for
a declaration a file writes, and not for one Lean makes for it, such as the unsafe copy of a
recursive definition, a `match` or the function of a structural recursion. -/
def written (env : Environment) (c : Name) : Bool :=
  (declRangeExt.find? (level := .exported) env c).isSome

/-- `READERS` for the definition or opaque constant `c` of a library module, whose type holds an
environment (`holdsEnv`): why the rule refuses it, if it does.

A declaration a file writes (`written`) passes when it is one of `stateless`; when it takes a proof
that the environment's extensions are loaded (`takesLoaded`); when its value begins with a guard
(`guardedValue`); or, for a recursive definition, whose value Lean replaces by a recursor or by a
default while its compiled code is its unsafe copy (`Compiler.mkUnsafeRecName`), when that copy's
value does. A guard tests the environment of the monad it runs in, so it does not pass a
declaration whose type also names an environment outright, as a parameter or a result: that
environment is another, and such a declaration passes only with the proof or by name. A
declaration Lean made is passed over when a declaration a file writes is named above it, which is
how Lean names what it makes for one, and refused otherwise. -/
def readerFault (env : Environment) (c : Name) (ci : ConstantInfo) : Option String :=
  if written env c then
    let copy := (env.find? (Compiler.mkUnsafeRecName c)).bind (·.value? (allowOpaque := true))
    let outright := ci.type.getUsedConstants.any fun k => k == ``Environment || k == ``Kernel.Environment
    let guarded := (ci.value? (allowOpaque := true)).any guardedValue || copy.any guardedValue
    if stateless.contains c || takesLoaded ci.type || (guarded && !outright) then none
    else if guarded then
      some "begins with the library's guard but is also handed an environment outright, which the guard does not test: it must take a proof of `LeanIntent.Loaded` for that environment"
    else some "is handed an environment and neither begins with `LeanIntent.asking` or `LeanIntent.askingIn` nor takes a proof of `LeanIntent.Loaded`, so it would answer from the state of Lean's environment extensions where that state is not loaded"
  else
    let rec above : Name → Bool
      | .anonymous => false
      | p@(.str q _) | p@(.num q _) =>
        written env p || written env (privateToUserName p) || above q
    if above c.getPrefix then none
    else some "is handed an environment, and no declaration a file writes accounts for it"

/-- Writes to the file `out` what `LOADED` finds in `file`, one of the tracked Lean files of the
project in the current directory, whose library is built into the directory `libDir`: a line for
each declaration of the file that names a function of `importChoices`, `+` and the declaration
where the rule accepts every such use, and otherwise, for each reason it refuses one, `-`, the
declaration and the reason. The declarations are those of the environment Lean's frontend makes of
the file (`elaborate`), its constants that no imported module declares. It is read by this program
in a process of its own, as a file's tests are (`moduleTests`), and from the file it writes rather
than from what its process prints. An error when the file declares no constant, since the rule
would then have read nothing of it. -/
unsafe def fileLoads (file libDir out : String) : IO Unit := do
  let files ← trackedLeanFiles
  let mods ← moduleNames files
  let some mod := (files.zip mods).find? (·.1 == file) |>.map (·.2)
    | throw <| IO.userError s!"{file} is not a Lean file Git's index lists here"
  initSearchPath (← findSysroot) [libDir]
  let opts := ({} : Options).setBool `Elab.async false
  let env := (← elaborate file file mod opts "so what it imports cannot be read").commandState.env
  let choices ← IO.ofExcept (importChoices env)
  let declared := env.constants.map₂.toList
  if declared.isEmpty then
    throw <| IO.userError s!"{file}: Lean's frontend shows no declaration of it, so what it imports cannot be read"
  let mut lines : Array String := #[]
  for (c, ci) in declared do
    let (names, faults) := loadsOf choices ci
    if names && faults.isEmpty then
      lines := lines.push s!"+ {c}"
    for fault in faults do
      lines := lines.push s!"- {c} {fault}"
  let sorted := (lines.map (·.replace "\n" " ")).qsort (· < ·)
  IO.FS.writeFile out (String.join (sorted.toList.map (· ++ "\n")))

/-- `LOADED` for the Lean files Git's index lists under `tools/`, each read by `fileLoads` in a
process of its own against the library built into `libDir`, into a directory removed afterwards.
The rule fails rather than passing when it finds no such file, or no declaration of them that
imports modules: this program is one of those files and imports the library's modules, so finding
none means the rule read nothing. -/
def checkToolLoads (libDir : System.FilePath) : IO (Array Rejection) := do
  let reject (message : String) : Rejection := { rule := "LOADED", message }
  let files := (← trackedLeanFiles).filter (·.startsWith "tools/")
  if files.isEmpty then
    return #[reject "Git's index lists no Lean file under tools/, where this program lies"]
  let out ← IO.FS.createTempDir
  try
    let mut errs : Array Rejection := #[]
    let mut importing := 0
    for h : i in [0:files.size] do
      let report := out / s!"{i}.loads"
      discard <| runSelf #["--loads", files[i], libDir.toString, report.toString]
      for l in ← IO.FS.lines report do
        importing := importing + 1
        if l.startsWith "- " then
          errs := errs.push (reject s!"{files[i]}: {(l.drop 2).toString}")
    if importing == 0 then
      errs := errs.push (reject "no declaration of a Lean file under tools/ is seen to import modules, though this program imports the library's: the rule read nothing")
    return errs
  finally
    IO.FS.removeDirAll out

/-- Every rule for the project in the current directory. `unsafe` because it imports the library's
modules with their environment extensions' state loaded, which Lean allows only after
`enableInitializersExecution`: that lets the import run the `initialize` declarations of the
library's modules in this process, as elaborating a file that imports them does. -/
unsafe def check : IO (Array Rejection) := do
  let config ← checkConfig
  unless config.isEmpty do
    return config
  let files ← libraryFiles
  if files.isEmpty then
    return #[{ rule := "LEAN-BUILD", message := "Git's index lists no Lean file of the library" }]
  let pkg ← loadConfig
  let mods ← moduleNames files
  let selected ← checkModules pkg files mods
  unless selected.isEmpty do
    return selected
  let notModules ← checkModuleFiles (← trackedLeanFiles)
  unless notModules.isEmpty do
    return notModules
  let built ← build files
  unless built.isEmpty do
    return built
  let codes ← checkCodes pkg.leanLibDir mods
  let toolLoads ← checkToolLoads pkg.leanLibDir
  initSearchPath (← findSysroot) [pkg.leanLibDir]
  enableInitializersExecution
  let env ← importModules (mods.map fun m => { module := m }) {} (loadExts := true)
  let choices ← IO.ofExcept (importChoices env)
  let idxs := mods.filterMap env.getModuleIdx?
  let mut errs : Array Rejection := #[]
  let mut audited := 0
  let mut compiled : Array Name := #[]
  let mut storedImports := false
  let mut holders : Std.HashMap Name Bool := {}
  let mut readers : Array Name := #[]
  for (c, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? c then
      if idxs.contains idx then
        audited := audited + 1
        let mod := env.header.moduleNames[idx.toNat]!
        errs := errs ++ (← auditConstant env mod c ci)
        let (names, faults) := loadsOf choices ci
        if c == storedImport then
          storedImports := names
        else
          for fault in faults do
            errs := errs.push { rule := "LOADED", message := s!"{mod}: {c} {fault}" }
        if ci matches .defnInfo _ | .opaqueInfo _ then
          let mut handed := false
          for k in ci.type.getUsedConstants do
            let (holds, known) := (holdsEnv env k).run holders
            holders := known
            if holds then
              handed := true
              break
          if handed then
            if written env c then
              readers := readers.push c
            if let some fault := readerFault env c ci then
              errs := errs.push { rule := "READERS", message := s!"{mod}: {c} {fault}" }
        if (IR.findEnvDecl env c).isSome then
          compiled := compiled.push c
  if readers.isEmpty then
    errs := errs.push { rule := "READERS", message :=
      "no declaration a library file writes is seen to be handed an environment, though its readers are: the rule read nothing" }
  for c in stateless do
    unless readers.contains c do
      errs := errs.push { rule := "READERS", message :=
        s!"the rule excepts {c}, which no library file declares as a declaration handed an environment: read the rule's exceptions again" }
  if audited == 0 then
    errs := errs.push { rule := "AXIOMS", message := "the library's modules declare no constant" }
  unless storedImports do
    errs := errs.push { rule := "LOADED", message :=
      s!"the library declares no {storedImport} that imports modules, the one declaration the rule lets import without loading the extensions' state: read the rule's exception again" }
  return errs ++ checkProcess env compiled ++ codes ++ toolLoads

end Check

/-- `unsafe` because every import this program makes loads the environment extensions' state: the
checks' import of the library's modules (`Check.check`), and Lean's frontend where it reads a file's
tests (`--tests-module`) or what a file imports (`--loads`). Lean allows that only after
`enableInitializersExecution`, which is `unsafe`: it lets an import run the `initialize`
declarations of the imported modules in this process, as Lean does when it elaborates a file that
imports them. -/
public unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["--tests"] =>
    for t in ← Check.projectTests do
      IO.println t
    return 0
  | ["--tests-module", file, out] =>
    Check.moduleTests file out
    return 0
  | ["--loads", file, libDir, out] =>
    Check.fileLoads file libDir out
    return 0
  | [] =>
    let errs ← Check.check
    for e in errs do
      IO.println s!"[{e.rule}] {e.message}"
    return if errs.isEmpty then 0 else 1
  | _ => throw <| IO.userError "usage: lean --run tools/check.lean [--tests | --tests-module <file> <out> | --loads <file> <libDir> <out>]"
