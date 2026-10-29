import Lean
import Lake
import Lake.Load.Package

/-!
# `check`: the repository's checks, and the listing of its tests

Run from the repository's top level as

    lean --run tools/check.lean            # the checks below
    lean --run tools/check.lean --tests    # the listing of tests, for no-mistakes

where `lean` is elan's, which runs the Lean that `lean-toolchain` names. It is not run through
`lake env`, so that it reads the project's configuration before Lake loads it. The checks exit with
status `0` when every rule holds, `1` when a rule rejects the project, and another non-zero status,
through an uncaught error, when they cannot run. Every input is read through the system that owns
it, never by reading source text by hand:

* the project's Lean files, from Git's index (`git ls-files`); the library's are every one of them
  outside `tools/`, which holds this program;
* the project's configuration, from Lake's own TOML parser (`Lake.Toml.loadToml`) and loader
  (`Lake.loadPackage`, which resolves no dependency);
* each file's module name, from Lean (`moduleNameOfFileName`), and its build, from Lake;
* the axioms each declaration rests on, from Lean (`collectAxioms`) over the environment Lean
  imports from the built modules.

The rules:

* `LAKE-CONFIG`: `lakefile.toml` sets only `name`, `defaultTargets`, `leanOptions` (with only
  `autoImplicit` and `relaxedAutoImplicit`) and `lean_lib` tables (with only `name`, `roots` and
  `globs`), and no `lakefile.lean` exists. So the package requires no other package and depends on
  nothing beyond Lean's own libraries, and Lake runs no code of the project to configure it.
* `LEAN-BUILD`: `lake build --wfail` builds every library file, given as its target, with no
  error and no warning. Lake rejects a file that is not a module of the workspace as an unknown
  target, and a `sorry` is a warning.
* `AXIOMS`: no library module declares an axiom, and every constant a library module declares rests
  only on `propext`, `Classical.choice` and `Quot.sound`, Lean's own axioms. So no claim the
  library makes about itself rests on `sorry` (`sorryAx`), on code run to decide it (the axiom
  `native_decide` adds to the module that uses it, asserting what that code returned) or on an
  axiom of the project. The library's modules must declare at least one constant.

The rules read what the build produced, so they hold only if no code the build runs was written to
defeat them: elaborating a Lean file runs the metaprograms it invokes.

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

/-- `LEAN-BUILD`: Lake builds every file of `files`, each given as its target, with warnings as
errors. -/
def build (files : Array String) : IO (Array Rejection) := do
  let (code, out) ← run "lake" (#["build", "--wfail"] ++ files)
  if code == 0 then
    return #[]
  return #[{ rule := "LEAN-BUILD", message :=
    s!"lake build --wfail of the library's Lean files failed; a file that is not a module of the workspace is an unknown target:\n{out}" }]

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
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let opts := (({} : Options).setBool `Elab.async false).setBool `debug.byAsSorry true
  let fail (messages : MessageLog) : IO (Array String) := do
    let shown ← messages.toList.mapM (·.toString)
    throw <| IO.userError s!"{path}: Lean could not elaborate it, so its tests cannot be read:\n{String.join shown}"
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


/-- Every rule for the project in the current directory. -/
def check : IO (Array Rejection) := do
  let config ← checkConfig
  unless config.isEmpty do
    return config
  let files ← libraryFiles
  if files.isEmpty then
    return #[{ rule := "LEAN-BUILD", message := "Git's index lists no Lean file of the library" }]
  let built ← build files
  unless built.isEmpty do
    return built
  let pkg ← loadConfig
  let mods ← moduleNames files
  initSearchPath (← findSysroot) [pkg.leanLibDir]
  let env ← importModules (mods.map fun m => { module := m }) {}
  let idxs := mods.filterMap env.getModuleIdx?
  let mut errs : Array Rejection := #[]
  let mut audited := 0
  for (c, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? c then
      if idxs.contains idx then
        audited := audited + 1
        errs := errs ++ (← auditConstant env env.header.moduleNames[idx.toNat]! c ci)
  if audited == 0 then
    errs := errs.push { rule := "AXIOMS", message := "the library's modules declare no constant" }
  return errs

end Check

/-- `unsafe` because reading a file's tests (`--tests-module`) runs Lean's frontend, which imports
the file's modules with their environment extensions only after `enableInitializersExecution`,
which is `unsafe`: it lets importing run the `initialize` declarations of the imported modules, as
elaborating them did. -/
unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["--tests"] =>
    for t in ← Check.projectTests do
      IO.println t
    return 0
  | ["--tests-module", file, out] =>
    Check.moduleTests file out
    return 0
  | [] =>
    let errs ← Check.check
    for e in errs do
      IO.println s!"[{e.rule}] {e.message}"
    return if errs.isEmpty then 0 else 1
  | _ => throw <| IO.userError "usage: lean --run tools/check.lean [--tests | --tests-module <file> <out>]"
