module

import Lean
import Lake
import Lake.Load.Package
import Std.Internal.UV.System
meta import Lake
meta import Lake.Load.Package

open Lean

namespace Check

structure Rejection where
  rule : String
  message : String

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def noCommentsPinFile : String := "tools/no-comments.pin"

def noCommentsConfigFile : String := ".no-comments.json"

def noCommentsRatchetFile : String := "tools/comment-ratchet.json"

def regulaPinFile : String := "tools/regula.pin"

def regulaRepoUrl : String := "https://github.com/rbeauchamp/regula.git"

def regulaProfile : String := "standard-logical"

def run (cmd : String) (args : Array String) : IO (UInt32 × String) := do
  let out ← IO.Process.output { cmd, args }
  return (out.exitCode, out.stdout ++ out.stderr)

def git (args : Array String) : IO String := do
  let o ← IO.Process.output { cmd := "git", args }
  unless o.exitCode == 0 do
    throw <| IO.userError s!"git {" ".intercalate args.toList} failed:\n{o.stderr}"
  return o.stdout

def trackedLeanFiles : IO (Array String) := do
  let out ← git #["ls-files", "-z", "--", "*.lean"]
  return ((out.splitOn "\x00").filter (· ≠ "")).toArray

def isToolFile (file : String) : Bool := file.startsWith "tools/"

def libraryFiles : IO (Array String) :=
  return (← trackedLeanFiles).filter (!isToolFile ·)

def moduleNames (files : Array String) : IO (Array Name) := do
  let cwd ← IO.currentDir
  files.mapM fun f => moduleNameOfFileName (System.FilePath.mk f) (some cwd)

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

def extraKeys (path : String) (allowed : List Name) (t : Lake.Toml.Table) : Array String :=
  t.items.filterMap fun (k, _) => if allowed.contains k then none else some s!"{path}{k}"

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

def hasDuplicateNames (xs : Array Name) : Bool := Id.run do
  let mut seen : Std.HashSet Name := {}
  for x in xs do
    if seen.contains x then
      return true
    seen := seen.insert x
  return false

def checkModules (pkg : Lake.Package) (files : Array String) (mods : Array Name) :
    IO (Array Rejection) := do
  let reject (message : String) : Rejection := { rule := "LEAN-BUILD", message }
  let mut errs : Array Rejection := #[]
  if hasDuplicateNames mods then
    errs := errs.push (reject "Git's index maps multiple tracked library files to the same module name")
  let mut selected : Array Name := #[]
  for lib in pkg.leanLibs do
    let libMods := (← lib.getModuleArray).map (·.name)
    if libMods.isEmpty then
      errs := errs.push (reject s!"the library target {lib.name} selects no module")
    unless pkg.defaultTargets.contains lib.name do
      errs := errs.push (reject s!"the library target {lib.name} is omitted from lakefile.toml defaultTargets")
    selected := selected ++ libMods
  if hasDuplicateNames pkg.defaultTargets then
    errs := errs.push (reject "lakefile.toml defaultTargets contains duplicate targets")
  for t in pkg.defaultTargets do
    unless pkg.leanLibs.any (·.name == t) do
      errs := errs.push (reject s!"lakefile.toml defaultTargets names {t}, which is not a library target")
  if hasDuplicateNames selected then
    errs := errs.push (reject "lakefile.toml library targets select duplicate modules")
  for (f, m) in files.zip mods do
    unless selected.contains m do
      errs := errs.push (reject s!"{f}, a library file Git's index lists, is the module {m}, which no library target selects, so a build of the targets does not build it")
  for m in selected do
    unless mods.contains m do
      errs := errs.push (reject s!"a library target selects the module {m}, whose file Git's index does not list, so these rules do not build or audit it")
  return errs

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

def build (files : Array String) : IO (Array Rejection) := do
  let (code, out) ← run "lake" (#["build", "--wfail"] ++ files)
  if code == 0 then
    return #[]
  return #[{ rule := "LEAN-BUILD", message :=
    s!"lake build --wfail of the library's Lean files failed; a file that is not a module of the workspace is an unknown target:\n{out}" }]

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

def axiomsOf (env : Environment) (c : Name) : IO (Array Name) :=
  (collectAxioms c : CoreM (Array Name)).toIO' { fileName := "<check>", fileMap := default } { env }

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

partial def atoms (stx : Syntax) (acc : Array String) : Array String :=
  match stx with
  | .atom _ val => acc.push val
  | .node _ _ args => args.foldl (fun acc arg => atoms arg acc) acc
  | _ => acc

partial def nodes (stx : Syntax) (acc : Array Syntax) : Array Syntax :=
  match stx with
  | .node _ _ args => args.foldl (fun acc arg => nodes arg acc) (acc.push stx)
  | _ => acc

def testsLean : String := "4.36.0"

def testTokens : List String :=
  ["#eval", "#eval!", "#guard", "run_cmd", "run_elab", "run_meta", "run_tac", "by_elab",
   "test_extern", "native_decide", "#guard_msgs", "#guard_panic", "#guard_expr", "#check_simp",
   "#check_tactic", "#check_tactic_failure"]

def otherTokens : List String :=
  ["#check", "#check_failure", "#check_assertions", "#synth", "#reduce", "#print", "#where",
   "#version", "#exit", "#import_path", "#show_deprecated_modules", "#dump_async_env_state",
   "#discr_tree_key", "#discr_tree_simp_key", "#grind_lint", "#widget", "#time", "#info_trees",
   "#with_exporting", "#v["]

def nativeConfig (n : Syntax) : Bool :=
  let item (kinds : List Name) (names : List Name) (m : Syntax) : Bool :=
    kinds.contains m.getKind && m[1].isIdent && names.contains m[1].getId.eraseMacroScopes
  let vals := [``Parser.Term.valConfigItem, ``Parser.Tactic.valConfigItem]
  item ([``Parser.Term.posConfigItem, ``Parser.Tactic.posConfigItem] ++ vals) [`native] n ||
    (n.getKind == ``Parser.Tactic.decide && (nodes n #[]).any (item vals [`config]))

def nameKey : Name → String
  | .anonymous => "_"
  | .str p s => nameKey p ++ "." ++ s.quote
  | .num p k => nameKey p ++ "." ++ toString k

partial def syntaxKey : Syntax → String
  | .missing => "?"
  | .atom _ val => val.quote
  | .ident _ _ n _ => "`" ++ nameKey n
  | .node _ k args => "(" ++ nameKey k ++ args.foldl (fun acc a => acc ++ " " ++ syntaxKey a) "" ++ ")"

unsafe def testsOfModule (path file : String) (mod : Name) (mods : Array Name)
    (out : System.FilePath) : IO (Array String) := do
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let opts := ({} : Options).setBool `Elab.async false
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
  if s.commandState.messages.reportedPlusUnreported.any (·.data.hasTag (· == `hasSorry)) then
    throw <| IO.userError s!"{path}: cannot inspect tests of a file using `sorry` or `debug.byAsSorry`"
  let env := s.commandState.env
  let modIdxs : Std.HashSet ModuleIdx := mods.foldl (init := {}) fun s m =>
    match env.getModuleIdx? m with
    | some idx => s.insert idx
    | none => s
  let declared (c : Name) : Bool :=
    match env.getModuleIdxFor? c with
    | some idx => modIdxs.contains idx
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
    let (syntaxes, elaborators, sawByAsSorry) := trees.foldl (init := (#[cmd], #[], false))
      fun acc tree => tree.foldInfo (init := acc) fun _ info (ss, es, byAsSorry) =>
        match info with
        | .ofCommandInfo i => (ss.push i.stx, es.push i.elaborator, byAsSorry)
        | .ofTermInfo i => (ss, es.push i.elaborator, byAsSorry)
        | .ofPartialTermInfo i => (ss, es.push i.elaborator, byAsSorry)
        | .ofTacticInfo i => (ss.push i.stx, es.push i.elaborator, byAsSorry)
        | .ofChoiceInfo i => (ss, es.push i.elaborator, byAsSorry)
        | .ofMacroExpansionInfo i => (ss.push i.output, es, byAsSorry)
        | .ofOptionInfo i => (ss, es, byAsSorry || i.optionName == `debug.byAsSorry)
        | _ => (ss, es, byAsSorry)
    if sawByAsSorry then
      throw <| IO.userError s!"{path}: cannot inspect tests when `debug.byAsSorry` is configured"
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

def importsOf (file : String) : IO (Array Name) := do
  let input ← IO.FS.readFile file
  let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext input file)
  if messages.hasErrors then
    throw <| IO.userError s!"{file}: Lean's parser could not read its header"
  return (Elab.headerToImports header).map (·.module)

partial def importOrder (n : Nat) (deps : Nat → Array Nat) : Option (Array Nat) :=
  let rec go (done : Array Nat) : Option (Array Nat) :=
    if done.size == n then some done
    else match (List.range n).find? fun i => !done.contains i && (deps i).all done.contains with
      | some i => go (done.push i)
      | none => none
  go #[]

def moduleTestsFile (out : System.FilePath) (mod : Name) : System.FilePath :=
  modToFilePath out mod "tests"

def runSelf (args : Array String) (cwd : Option System.FilePath := none) : IO (Array String) := do
  let top := System.FilePath.mk (← git #["rev-parse", "--show-toplevel"]).trimAscii.toString
  let script := top / "tools" / "check.lean"
  let o ← IO.Process.output { cmd := "lean", args := #["--run", script.toString] ++ args, cwd }
  unless o.exitCode == 0 do
    throw <| IO.userError s!"lean --run tools/check.lean {" ".intercalate args.toList} exited with status {o.exitCode}:\n{o.stderr}{o.stdout}"
  return ((o.stdout.splitOn "\n").filter (· ≠ "")).toArray

unsafe def moduleTests (file out : String) : IO Unit := do
  let files ← trackedLeanFiles
  let mods ← moduleNames files
  let some mod := (files.zip mods).find? (·.1 == file) |>.map (·.2)
    | throw <| IO.userError s!"{file} is not a Lean file Git's index lists here"
  let pre := (← git #["rev-parse", "--show-prefix"]).trimAscii.toString
  initSearchPath (← findSysroot) [out]
  let tests ← testsOfModule (pre ++ file) file mod mods out
  IO.FS.writeFile (moduleTestsFile out mod) (String.join (tests.toList.map (· ++ "\n")))

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

def boundQueries : List (Name × String) :=
  [(``IO.Process.spawn, "lean_io_process_spawn"), (``IO.appPath, "lean_io_app_path"),
   (``IO.currentDir, "lean_io_current_dir"),
   (``IO.Process.getCurrentDir, "lean_io_process_get_current_dir"),
   (``IO.getEnv, "lean_io_getenv"),
   (``Std.Internal.UV.System.exePath, "lean_uv_exepath"),
   (``Std.Internal.UV.System.cwd, "lean_uv_cwd"),
   (``Std.Internal.UV.System.osGetenv, "lean_uv_os_getenv"),
   (``Std.Internal.UV.System.osEnviron, "lean_uv_os_environ"),
   (``Std.Internal.UV.System.osHomedir, "lean_uv_os_homedir"),
   (``Std.Internal.UV.System.osTmpdir, "lean_uv_os_tmpdir"),
   (``Std.Internal.UV.System.osGetPasswd, "lean_uv_os_get_passwd"),
   (``Std.Internal.UV.System.osGetHostname, "lean_uv_os_gethostname"),
   (``Std.Internal.UV.System.osUname, "lean_uv_os_uname")]

def processQueries : List String :=
  boundQueries.map (·.2)

def notFollowed : List Name := [`Lean.manualRoot]

def bindsTo (symbol : String) : ExternEntry → Bool
  | .standard _ fn => fn == symbol
  | .inline _ pattern => (pattern.splitOn symbol).length > 1
  | _ => false

def checkProcess (env : Environment) (roots : Array Name) : Array Rejection := Id.run do
  let reject (message : String) : Rejection := { rule := "PROCESS", message }
  let mut errs : Array Rejection := #[]
  unless Lean.versionString == testsLean do
    errs := errs.push <| reject s!"PROCESS checks extern bindings audited for Lean {testsLean}, not Lean {Lean.versionString}, which runs here: read processQueries again from Init and Std.Internal.UV.System extern attributes"
  if roots.isEmpty then
    return errs.push <| reject "the library's modules hold no compiled code"
  for (decl, symbol) in boundQueries do
    let bound := match IR.findEnvDecl env decl with
      | some (.extern _ _ _ data) => data.entries.any (bindsTo symbol)
      | _ => false
    unless bound do
      errs := errs.push <| reject s!"{decl} is not bound to {symbol} under this Lean: read processQueries again from its extern attributes"
  let mut parent : Std.HashMap Name Name := roots.foldl (fun m r => m.insert r r) {}
  let mut queue := roots
  let mut next := 0
  let path (parent : Std.HashMap Name Name) (c : Name) : List Name := Id.run do
    let mut out := [c]
    let mut at' := c
    for _ in [0:parent.size] do
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

def isLowerHex (len : Nat) (s : String) : Bool :=
  s.length == len && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

def isSha256 (s : String) : Bool :=
  isLowerHex 64 s

def isSha1 (s : String) : Bool :=
  isLowerHex 40 s

def isValidReleaseTag (s : String) : Bool :=
  s.startsWith "v" && s.length > 1 && !s.contains ".." &&
    s.all fun c => c.isAlphanum || c == '.' || c == '-'

def parsePinLines (path raw : String) : Except String (List (String × String)) := do
  if raw.contains '\r' then
    throw s!"{path}: expected LF line endings"
  let lines := if raw.endsWith "\n" then (raw.splitOn "\n").dropLast else raw.splitOn "\n"
  if lines.isEmpty then
    throw s!"{path}: file is empty"
  lines.mapM fun line =>
    match line.splitOn "=" with
    | [k, v] => return (k, v)
    | _ => throw s!"{path}: expected KEY=VALUE line, got {line.quote}"

structure NoCommentsPin where
  version : String
  darwinArm64Sha256 : String
  linuxX86_64Sha256 : String

def parseNoCommentsPin (raw : String) : Except String NoCommentsPin := do
  let mut version? : Option String := none
  let mut darwin? : Option String := none
  let mut linux? : Option String := none
  for (k, v) in ← parsePinLines noCommentsPinFile raw do
    match k with
    | "VERSION" =>
      if version?.isSome then
        throw s!"{noCommentsPinFile}: duplicate VERSION key"
      unless isValidReleaseTag v do
        throw s!"{noCommentsPinFile}: invalid VERSION {v.quote}"
      version? := some v
    | "DARWIN_ARM64_SHA256" =>
      if darwin?.isSome then
        throw s!"{noCommentsPinFile}: duplicate DARWIN_ARM64_SHA256 key"
      unless isSha256 v do
        throw s!"{noCommentsPinFile}: invalid DARWIN_ARM64_SHA256 {v.quote}"
      darwin? := some v
    | "LINUX_X86_64_SHA256" =>
      if linux?.isSome then
        throw s!"{noCommentsPinFile}: duplicate LINUX_X86_64_SHA256 key"
      unless isSha256 v do
        throw s!"{noCommentsPinFile}: invalid LINUX_X86_64_SHA256 {v.quote}"
      linux? := some v
    | _ =>
      throw s!"{noCommentsPinFile}: unknown key {k.quote}"
  let some version := version?
    | throw s!"{noCommentsPinFile}: missing VERSION"
  let some darwinArm64Sha256 := darwin?
    | throw s!"{noCommentsPinFile}: missing DARWIN_ARM64_SHA256"
  let some linuxX86_64Sha256 := linux?
    | throw s!"{noCommentsPinFile}: missing LINUX_X86_64_SHA256"
  return { version, darwinArm64Sha256, linuxX86_64Sha256 }

structure RegulaPin where
  version : String
  commit : String

def parseRegulaPin (raw : String) : Except String RegulaPin := do
  let mut version? : Option String := none
  let mut commit? : Option String := none
  for (k, v) in ← parsePinLines regulaPinFile raw do
    match k with
    | "VERSION" =>
      if version?.isSome then
        throw s!"{regulaPinFile}: duplicate VERSION key"
      unless isValidReleaseTag v do
        throw s!"{regulaPinFile}: invalid VERSION {v.quote}"
      version? := some v
    | "COMMIT" =>
      if commit?.isSome then
        throw s!"{regulaPinFile}: duplicate COMMIT key"
      unless isSha1 v do
        throw s!"{regulaPinFile}: invalid COMMIT {v.quote}"
      commit? := some v
    | _ =>
      throw s!"{regulaPinFile}: unknown key {k.quote}"
  let some version := version?
    | throw s!"{regulaPinFile}: missing VERSION"
  let some commit := commit?
    | throw s!"{regulaPinFile}: missing COMMIT"
  return { version, commit }

structure BaseRef where
  value : String
  nonEmpty : value ≠ ""
  notFlag : !value.startsWith "-" = true

def BaseRef.parse (raw : String) : Except String BaseRef :=
  if h1 : raw = "" then
    .error s!"invalid --base-ref value: {raw.quote}"
  else if h2 : raw.startsWith "-" then
    .error s!"invalid --base-ref value: {raw.quote}"
  else
    .ok ⟨raw, h1, by simp [h2]⟩

structure CheckOpts where
  baseRef? : Option BaseRef := none

def isRegularGitMode (mode : String) : Bool :=
  mode == "100644" || mode == "100755"

inductive GitIndexEntry where
  | absent
  | regular (oid : String)
  | invalid (detail : String)

def parseGitIndexHeader (expectedPath path : String) (fields : List String) : Option String :=
  match fields with
  | [mode, oid, "0"] =>
    if path == expectedPath && isRegularGitMode mode && oid != "" then some oid else none
  | _ => none

def parseGitIndexEntry (expectedPath raw : String) : GitIndexEntry :=
  match raw.splitOn "\x00" with
  | [""] => .absent
  | [entry, ""] =>
    match entry.splitOn "\t" with
    | [header, path] =>
      match parseGitIndexHeader expectedPath path (header.splitOn " ") with
      | some oid => .regular oid
      | none => .invalid entry
    | _ => .invalid entry
  | _ => .invalid (raw.replace "\x00" "; ")

theorem parseGitIndexHeader_eq_some_iff (expectedPath path oid : String) (fields : List String) :
    parseGitIndexHeader expectedPath path fields = some oid ↔
      path = expectedPath ∧
      oid ≠ "" ∧
      ∃ mode, (mode = "100644" ∨ mode = "100755") ∧ fields = [mode, oid, "0"] := by
  unfold parseGitIndexHeader isRegularGitMode
  constructor
  · intro h
    split at h
    · split at h
      · rename_i mode _ hc
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hc
        exact ⟨hc.1.1, hc.2, mode, hc.1.2, rfl⟩
      · cases h
    · cases h
  · rintro ⟨rfl, hoid, mode, hmode, rfl⟩
    rcases hmode with rfl | rfl <;> simp [hoid]

theorem parseGitIndexEntry_regular_iff (expectedPath raw oid : String) :
    parseGitIndexEntry expectedPath raw = .regular oid ↔
      ∃ entry header mode,
        raw.splitOn "\x00" = [entry, ""] ∧
        entry.splitOn "\t" = [header, expectedPath] ∧
        (mode = "100644" ∨ mode = "100755") ∧
        oid ≠ "" ∧
        header.splitOn " " = [mode, oid, "0"] := by
  unfold parseGitIndexEntry
  constructor
  · intro h
    split at h
    · cases h
    · rename_i entry hr
      split at h
      · rename_i header path ht
        split at h
        · rename_i oid' hh
          cases h
          have ⟨hp, hoid, mode, hmode, hf⟩ :=
            (parseGitIndexHeader_eq_some_iff expectedPath path oid (header.splitOn " ")).mp hh
          subst hp
          exact ⟨entry, header, mode, hr, ht, hmode, hoid, hf⟩
        · cases h
      · cases h
    · cases h
  · rintro ⟨entry, header, mode, hr, ht, hmode, hoid, hf⟩
    have hh :=
      (parseGitIndexHeader_eq_some_iff expectedPath expectedPath oid (header.splitOn " ")).mpr
        ⟨rfl, hoid, mode, hmode, hf⟩
    simp [hr, ht, hh]

def checkWorkingTreeRegularFile (path : String) : IO (Option String) := do
  let comps := path.splitOn "/"
  if comps.any (fun c => c.isEmpty || c == "." || c == "..") then
    return some s!"{path} is not a normalized relative path"
  match comps with
  | [] => return some s!"{path} is not a normalized relative path"
  | first :: rest => walk first rest ""
where
  walk (seg : String) (rest : List String) (cur : String) : IO (Option String) := do
    let dir : System.FilePath := if cur.isEmpty then "." else cur
    let entries ← try dir.readDir catch _ => return some s!"cannot list directory {dir} for {path}"
    unless entries.any (·.fileName == seg) do
      return some s!"{path} does not exist in the working tree with that exact spelling"
    let next := if cur.isEmpty then seg else s!"{cur}/{seg}"
    let info ← try System.FilePath.symlinkMetadata next catch _ =>
      return some s!"cannot inspect {next} in the working tree"
    match rest with
    | [] =>
      unless info.type == .file do
        return some s!"{path} is not a regular file in the working tree"
      return none
    | nextSeg :: tl =>
      unless info.type == .dir do
        return some s!"{next} is not a directory in the working tree"
      walk nextSeg tl next

def checkCommittedRegularFile (path : String) : IO (Option String) := do
  let staged ← git #["ls-files", "--stage", "-z", "--full-name", "--", path]
  match parseGitIndexEntry path staged with
  | .absent =>
    return some s!"{path} is not tracked at that exact path in Git's index"
  | .invalid detail =>
    return some s!"{path} is not a regular staged file at that exact path in Git's index ({detail})"
  | .regular _ =>
    checkWorkingTreeRegularFile path

def defaultBaseRefs : List String :=
  ["refs/remotes/origin/main", "refs/heads/main"]

def resolveCommit (ref : String) : IO (Option String) := do
  let known ← IO.Process.output
    { cmd := "git", args := #["rev-parse", "--verify", "--quiet", "--end-of-options", ref ++ "^{commit}"] }
  if known.exitCode == 0 then
    return some known.stdout.trimAscii.toString
  else if known.exitCode == 1 then
    return none
  else
    throw <| IO.userError s!"NO-COMMENTS: git rev-parse for {ref} failed:\n{known.stderr}"

def exactRefExists (fullRef : String) : IO Bool := do
  let res ← IO.Process.output
    { cmd := "git", args := #["show-ref", "--verify", "--quiet", "--", fullRef] }
  if res.exitCode == 0 then
    return true
  else if res.exitCode == 1 then
    return false
  else
    throw <| IO.userError s!"NO-COMMENTS: git show-ref for {fullRef} failed:\n{res.stderr}"

def resolveDefaultBaseCommit : IO String := do
  for ref in defaultBaseRefs do
    if ← exactRefExists ref then
      let some sha ← resolveCommit ref
        | throw <| IO.userError s!"NO-COMMENTS: default base ref {ref} does not name a commit"
      match BaseRef.parse sha with
      | .ok base => return base.value
      | .error e =>
        throw <| IO.userError s!"NO-COMMENTS: default base ref {ref} resolved to invalid commit ({e})"
  throw <| IO.userError "NO-COMMENTS: neither refs/remotes/origin/main nor refs/heads/main names a commit; fetch the base branch or pass --base-ref <ref>"

def readNoCommentsPin : IO NoCommentsPin := do
  let raw ← IO.FS.readFile noCommentsPinFile
  match parseNoCommentsPin raw with
  | .ok pin => return pin
  | .error e => throw <| IO.userError s!"NO-COMMENTS: {e}"

def platformAsset (pin : NoCommentsPin) : IO (String × String) := do
  let target := System.Platform.target
  let arch ←
    if target.isEmpty then
      let o ← IO.Process.output { cmd := "uname", args := #["-m"] }
      if o.exitCode == 0 then pure o.stdout.trimAscii.toString else pure ""
    else pure ""
  if System.Platform.isOSX then
    if target.startsWith "arm64-" || target.startsWith "aarch64-" ||
        (target.isEmpty && (arch == "arm64" || arch == "aarch64")) then
      return ("no-comments-darwin-arm64", pin.darwinArm64Sha256)
    throw <| IO.userError s!"NO-COMMENTS: unsupported macOS target {target.quote} (pinned release supports darwin-arm64 and linux-x86_64)"
  if System.Platform.isLinux then
    if target.startsWith "x86_64-" || (target.isEmpty && arch == "x86_64") then
      return ("no-comments-linux-x86_64", pin.linuxX86_64Sha256)
    throw <| IO.userError s!"NO-COMMENTS: unsupported Linux target {target.quote} (pinned release supports darwin-arm64 and linux-x86_64)"
  throw <| IO.userError s!"NO-COMMENTS: unsupported platform target {target.quote} (pinned release supports darwin-arm64 and linux-x86_64)"

def parseSha256Output (tool raw : String) : IO String := do
  let firstLine := (raw.splitOn "\n").headD ""
  let tokens := ((firstLine.replace "\t" " ").splitOn " ").filter (· ≠ "")
  match tokens with
  | digest :: _ =>
    if isSha256 digest then
      return digest
    throw <| IO.userError s!"NO-COMMENTS: {tool} produced invalid SHA-256 digest {digest.quote}"
  | [] =>
    throw <| IO.userError s!"NO-COMMENTS: {tool} produced empty output"

def sha256Cmd (rule : String) : IO (String × Array String) := do
  if System.Platform.isOSX then
    return ("shasum", #["-a", "256"])
  else if System.Platform.isLinux then
    return ("sha256sum", #[])
  else
    throw <| IO.userError s!"{rule}: unsupported platform target {System.Platform.target.quote} for SHA-256 verification"

def sha256File (path : System.FilePath) : IO String := do
  let (cmd, baseArgs) ← sha256Cmd "NO-COMMENTS"
  let o ← IO.Process.output { cmd, args := baseArgs ++ #["--", path.toString] }
  unless o.exitCode == 0 do
    throw <| IO.userError s!"NO-COMMENTS: {cmd} failed on {path}:\n{o.stderr}"
  parseSha256Output cmd o.stdout

def sha256Batch (rule : String) (paths : Array String) : IO (Array String) := do
  if paths.isEmpty then
    return #[]
  let (cmd, baseArgs) ← sha256Cmd rule
  let o ← IO.Process.output { cmd, args := baseArgs ++ #["--"] ++ paths }
  unless o.exitCode == 0 do
    throw <| IO.userError s!"{rule}: {cmd} failed:\n{o.stderr}"
  unless o.stdout.endsWith "\n" do
    throw <| IO.userError s!"{rule}: {cmd} output did not end with newline"
  let lines := (o.stdout.splitOn "\n").dropLast.toArray
  unless lines.size == paths.size do
    throw <| IO.userError s!"{rule}: {cmd} returned {lines.size} lines for {paths.size} paths"
  let mut digests : Array String := #[]
  for (arg, line) in paths.zip lines do
    let some digestSlice := line.dropSuffix? ("  " ++ arg)
      | throw <| IO.userError s!"{rule}: {cmd} returned unexpected output line for {arg.quote}: {line.quote}"
    let digest := digestSlice.toString
    unless isSha256 digest do
      throw <| IO.userError s!"{rule}: {cmd} produced invalid SHA-256 digest {digest.quote}"
    digests := digests.push digest
  return digests

def buildPathPrefixes (isAbs : Bool) : List String → Option (List String × String)
  | [] => none
  | first :: rest =>
    let p0 := if isAbs then "/" ++ first else first
    some (go [] p0 rest)
where
  go (acc : List String) (cur : String) : List String → List String × String
    | [] => (acc.reverse, cur)
    | seg :: tl => go (cur :: acc) (cur ++ "/" ++ seg) tl

def splitRegularPath (raw : String) : Except String (List String × String) :=
  if raw.isEmpty then
    .error "path is empty"
  else if raw.contains '\x00' then
    .error "path contains NUL byte"
  else if raw.startsWith "//" then
    .error "path starts with '//'"
  else if raw.endsWith "/" then
    .error "path ends with '/'"
  else
    let isAbs := raw.startsWith "/"
    let segs := (raw.splitOn "/").filter (· ≠ "")
    match buildPathPrefixes isAbs segs with
    | some res => .ok res
    | none => .error "path has no components"

def checkNoSymlinkPath (rule label raw : String) (expected : IO.FS.FileType) (what : String) :
    IO System.FilePath := do
  let (dirPrefixes, finalPath) ← match splitRegularPath raw with
    | .ok res => pure res
    | .error e => throw <| IO.userError s!"{rule}: {label} ({raw.quote}) is invalid: {e}"
  for p in dirPrefixes do
    let info ← try System.FilePath.symlinkMetadata p catch _ =>
      throw <| IO.userError s!"{rule}: {label} ({raw.quote}) cannot inspect path component {p.quote}"
    unless info.type == .dir do
      throw <| IO.userError s!"{rule}: {label} ({raw.quote}) traverses non-directory or symlink component {p.quote}"
  let info ← try System.FilePath.symlinkMetadata finalPath catch _ =>
    throw <| IO.userError s!"{rule}: {label} ({raw.quote}) does not exist or cannot be inspected"
  unless info.type == expected do
    throw <| IO.userError s!"{rule}: {label} ({raw.quote}) is not {what} (symlinks are rejected)"
  return System.FilePath.mk finalPath

def checkNoSymlinkRegularFile (label raw : String) : IO System.FilePath :=
  checkNoSymlinkPath "NO-COMMENTS" label raw .file "a regular file"

def checkNoSymlinkDir (rule label raw : String) : IO System.FilePath :=
  checkNoSymlinkPath rule label raw .dir "a directory"

def copyFileBytes (src dst : System.FilePath) : IO Unit := do
  let hIn ← IO.FS.Handle.mk src .read
  let hOut ← IO.FS.Handle.mk dst .write
  repeat
    let chunk ← hIn.read 262144
    if chunk.isEmpty then
      break
    hOut.write chunk
  hOut.flush

def noCommentsCacheDirPrefixes (expectedSha : String) : List String :=
  [".lake", ".lake/cache", ".lake/cache/no-comments", s!".lake/cache/no-comments/{expectedSha}"]

def noCommentsCacheBinPath (expectedSha : String) : System.FilePath :=
  System.FilePath.mk s!".lake/cache/no-comments/{expectedSha}/no-comments"

def checkDirChain (rule : String) (prefixes : List String) : IO Unit := do
  for p in prefixes do
    let info ← try System.FilePath.symlinkMetadata p catch _ =>
      throw <| IO.userError s!"{rule}: cache directory {p} does not exist or cannot be inspected"
    unless info.type == .dir do
      throw <| IO.userError s!"{rule}: cache path {p} is not a real directory (symlinks are rejected)"

def ensureDirChain (rule : String) (prefixes : List String) : IO Unit := do
  for p in prefixes do
    let existing? ← try
      some <$> System.FilePath.symlinkMetadata p
    catch
      | .noFileOrDirectory .. => pure none
      | e => throw e
    match existing? with
    | some info =>
      unless info.type == .dir do
        throw <| IO.userError s!"{rule}: cache path {p} is not a real directory (symlinks are rejected)"
    | none =>
      try
        IO.FS.createDir p
      catch
        | .alreadyExists .. =>
          let raced ← try System.FilePath.symlinkMetadata p catch _ =>
            throw <| IO.userError s!"{rule}: cannot inspect cache directory {p} after concurrent creation"
          unless raced.type == .dir do
            throw <| IO.userError s!"{rule}: cache path {p} is not a real directory (symlinks are rejected)"
        | e =>
          throw <| IO.userError s!"{rule}: failed to create cache directory {p}: {e}"
      let created ← try System.FilePath.symlinkMetadata p catch _ =>
        throw <| IO.userError s!"{rule}: cannot inspect cache directory {p} after creation"
      unless created.type == .dir do
        throw <| IO.userError s!"{rule}: cache path {p} is not a real directory (symlinks are rejected)"

def verifyExistingDirChain (rule : String) (prefixes : List String) : IO Bool := do
  for p in prefixes do
    let existing? ← try
      some <$> System.FilePath.symlinkMetadata p
    catch
      | .noFileOrDirectory .. => pure none
      | e => throw e
    match existing? with
    | none => return false
    | some info =>
      unless info.type == .dir do
        throw <| IO.userError s!"{rule}: cache path {p} is not a real directory (symlinks are rejected)"
  return true

def checkCacheDirChain (expectedSha : String) : IO Unit :=
  checkDirChain "NO-COMMENTS" (noCommentsCacheDirPrefixes expectedSha)

def ensureNoCommentsCacheDir (expectedSha : String) : IO System.FilePath := do
  ensureDirChain "NO-COMMENTS" (noCommentsCacheDirPrefixes expectedSha)
  return System.FilePath.mk s!".lake/cache/no-comments/{expectedSha}"

def verifyNoCommentsCachePath (expectedSha : String) : IO (Option System.FilePath) := do
  unless ← verifyExistingDirChain "NO-COMMENTS" (noCommentsCacheDirPrefixes expectedSha) do
    return none
  let cacheBin := noCommentsCacheBinPath expectedSha
  let binInfo? ← try
    some <$> cacheBin.symlinkMetadata
  catch
    | .noFileOrDirectory .. => pure none
    | e => throw e
  let some info := binInfo? | return none
  unless info.type == .file do
    throw <| IO.userError s!"NO-COMMENTS: cached binary path {cacheBin} is not a regular file (symlinks are rejected)"
  let actual ← sha256File cacheBin
  unless actual == expectedSha do
    throw <| IO.userError s!"NO-COMMENTS: cached binary {cacheBin} SHA-256 mismatch: expected {expectedSha}, got {actual}"
  return some cacheBin

def stageNoCommentsBin (expectedSha sourceLabel : String) (populate : System.FilePath → IO Unit) :
    IO System.FilePath := do
  let cacheDir ← ensureNoCommentsCacheDir expectedSha
  let cacheBin := noCommentsCacheBinPath expectedSha
  let preBin? ← try
    some <$> cacheBin.symlinkMetadata
  catch
    | .noFileOrDirectory .. => pure none
    | e => throw e
  if let some info := preBin? then
    unless info.type == .file do
      throw <| IO.userError s!"NO-COMMENTS: cached binary path {cacheBin} is not a regular file (symlinks are rejected)"
  let mk ← IO.Process.output { cmd := "mktemp", args := #[(cacheDir / "no-comments.tmp.XXXXXX").toString] }
  unless mk.exitCode == 0 do
    throw <| IO.userError s!"NO-COMMENTS: mktemp failed in {cacheDir}:\n{mk.stderr}"
  let tmpRaw := mk.stdout.trimAscii.toString
  let expectedPrefix := cacheDir.toString ++ "/no-comments.tmp."
  unless tmpRaw.startsWith expectedPrefix && (tmpRaw.splitOn "/").length == 5 do
    throw <| IO.userError s!"NO-COMMENTS: mktemp returned unexpected staging path {tmpRaw.quote}"
  let tmpPath := System.FilePath.mk tmpRaw
  try
    let tmpPre ← try tmpPath.symlinkMetadata catch _ =>
      throw <| IO.userError s!"NO-COMMENTS: staging file {tmpPath} cannot be inspected"
    unless tmpPre.type == .file do
      throw <| IO.userError s!"NO-COMMENTS: staging path {tmpPath} is not a regular file"
    populate tmpPath
    let tmpPost ← try tmpPath.symlinkMetadata catch _ =>
      throw <| IO.userError s!"NO-COMMENTS: staging file {tmpPath} cannot be inspected after staging"
    unless tmpPost.type == .file do
      throw <| IO.userError s!"NO-COMMENTS: staging path {tmpPath} is not a regular file after staging"
    let actual ← sha256File tmpPath
    unless actual == expectedSha do
      throw <| IO.userError s!"NO-COMMENTS: {sourceLabel} SHA-256 mismatch: expected {expectedSha}, got {actual}"
    IO.setAccessRights tmpPath {
      user := { read := true, write := true, execution := true }
      group := { read := true, execution := true }
      other := { read := true, execution := true }
    }
    checkCacheDirChain expectedSha
    let preRenameBin? ← try
      some <$> cacheBin.symlinkMetadata
    catch
      | .noFileOrDirectory .. => pure none
      | e => throw e
    if let some info := preRenameBin? then
      unless info.type == .file do
        throw <| IO.userError s!"NO-COMMENTS: cached binary path {cacheBin} is not a regular file (symlinks are rejected)"
    IO.FS.rename tmpPath cacheBin
    let some verified ← verifyNoCommentsCachePath expectedSha
      | throw <| IO.userError s!"NO-COMMENTS: cached binary {cacheBin} missing after staging"
    return verified
  finally
    try
      IO.FS.removeFile tmpPath
    catch _ => pure ()

def ensureNoCommentsBin (pin : NoCommentsPin) : IO System.FilePath := do
  let (assetName, expectedSha) ← platformAsset pin
  match ← IO.getEnv "NO_COMMENTS_BIN" with
  | some raw =>
    let verifiedSrc ← checkNoSymlinkRegularFile "NO_COMMENTS_BIN" raw
    stageNoCommentsBin expectedSha s!"NO_COMMENTS_BIN ({raw.quote})" fun tmpPath =>
      copyFileBytes verifiedSrc tmpPath
  | none =>
    if let some cacheBin ← verifyNoCommentsCachePath expectedSha then
      return cacheBin
    let url := s!"https://github.com/rbeauchamp/lean-no-comments/releases/download/{pin.version}/{assetName}"
    stageNoCommentsBin expectedSha s!"downloaded {assetName} ({pin.version})" fun tmpPath => do
      let dl ← IO.Process.output {
        cmd := "curl"
        args := #[
          "-sSfL", "--proto", "=https", "--tlsv1.2",
          "--connect-timeout", "15", "--retry", "2", "--retry-delay", "2",
          "--speed-time", "30", "--speed-limit", "1024",
          "-o", tmpPath.toString, "--", url
        ]
      }
      unless dl.exitCode == 0 do
        throw <| IO.userError s!"NO-COMMENTS: failed to download {url}:\n{dl.stderr}"

def checkComments (opts : CheckOpts) : IO (Array Rejection) := do
  let mut admissionErrs : Array Rejection := #[]
  for path in [noCommentsPinFile, noCommentsConfigFile, noCommentsRatchetFile] do
    if let some err ← checkCommittedRegularFile path then
      admissionErrs := admissionErrs.push { rule := "NO-COMMENTS", message := err }
  unless admissionErrs.isEmpty do
    return admissionErrs
  let pin ← readNoCommentsPin
  let bin ← ensureNoCommentsBin pin
  let baseRefArg ← match opts.baseRef? with
    | some ref => pure ref.value
    | none => resolveDefaultBaseCommit
  let args := #["check", "--base-ref", baseRefArg]
  let out ← IO.Process.output { cmd := bin.toString, args }
  if out.exitCode == 0 then
    return #[]
  let raw := (out.stderr ++ "\n" ++ out.stdout).trimAscii.toString
  let lines := (((raw.splitOn "\n").map (·.trimAscii.toString)).filter (· ≠ "")).toArray
  if lines.isEmpty then
    return #[{ rule := "NO-COMMENTS", message := s!"{bin} check exited with status {out.exitCode}" }]
  return lines.map fun l => { rule := "NO-COMMENTS", message := l }

def listComments (target? : Option String) : IO Unit := do
  let configErrs ← checkConfig
  unless configErrs.isEmpty do
    let details := "\n".intercalate (configErrs.toList.map fun e => s!"[{e.rule}] {e.message}")
    throw <| IO.userError details
  for path in [noCommentsPinFile, noCommentsConfigFile] do
    if let some err ← checkCommittedRegularFile path then
      throw <| IO.userError s!"NO-COMMENTS: {err}"
  let pin ← readNoCommentsPin
  let bin ← ensureNoCommentsBin pin
  let args := match target? with
    | none => #["inventory"]
    | some file => #["inventory", "--file", file]
  let out ← IO.Process.output { cmd := bin.toString, args }
  unless out.stdout.isEmpty do
    IO.print out.stdout
  unless out.exitCode == 0 do
    let detail := out.stderr.trimAscii.toString
    throw <| IO.userError (if detail.isEmpty then s!"{bin} inventory exited with status {out.exitCode}" else detail)

def readRegulaPin : IO RegulaPin := do
  let raw ← IO.FS.readFile regulaPinFile
  match parseRegulaPin raw with
  | .ok pin => return pin
  | .error e => throw <| IO.userError s!"REGULA: {e}"

def regulaBasePrefixes : List String :=
  [".lake", ".lake/cache", ".lake/cache/regula"]

def regulaCacheDirPath (commit : String) : System.FilePath :=
  System.FilePath.mk s!".lake/cache/regula/{commit}"

def regulaCachePrefixes (commit : String) : List String :=
  regulaBasePrefixes ++ [s!".lake/cache/regula/{commit}"]

def gitIn (dir : System.FilePath) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "git", args := #["-C", dir.toString, "-c", "core.fsmonitor=false"] ++ args }

def checkRegularChildFile (rule : String) (dir : System.FilePath) (rel : String) : IO Unit := do
  let path := dir / rel
  let info ← try path.symlinkMetadata catch _ =>
    throw <| IO.userError s!"{rule}: {path} does not exist or cannot be inspected"
  unless info.type == .file do
    throw <| IO.userError s!"{rule}: {path} is not a regular file (symlinks are rejected)"

def checkAbsentPath (rule : String) (dir : System.FilePath) (rel : String) : IO Unit := do
  let path := dir / rel
  let info? ← try
    some <$> path.symlinkMetadata
  catch
    | .noFileOrDirectory .. => pure none
    | e => throw e
  if info?.isSome then
    throw <| IO.userError s!"{rule}: {path} must not exist in checkout"

def verifyRegulaCheckout (pin : RegulaPin) (dir : System.FilePath) (checkTag checkIgnored : Bool) : IO Unit := do
  checkRegularChildFile "REGULA" dir "lakefile.toml"
  checkRegularChildFile "REGULA" dir "lean-toolchain"
  checkAbsentPath "REGULA" dir "lakefile.lean"
  let gitMeta ← try (dir / ".git").symlinkMetadata catch _ =>
    throw <| IO.userError s!"REGULA: {dir / ".git"} does not exist or cannot be inspected"
  unless gitMeta.type == .dir do
    throw <| IO.userError s!"REGULA: {dir / ".git"} must be a real directory (symlinks and gitfiles are rejected)"
  let headOut ← gitIn dir #["rev-parse", "--verify", "--quiet", "--end-of-options", "HEAD^{commit}"]
  unless headOut.exitCode == 0 do
    throw <| IO.userError s!"REGULA: git rev-parse HEAD failed in {dir}:\n{headOut.stderr}"
  let actualHead := headOut.stdout.trimAscii.toString
  unless actualHead == pin.commit do
    throw <| IO.userError s!"REGULA: checkout {dir} HEAD {actualHead.quote} does not match pinned commit {pin.commit.quote}"
  if checkTag then
    let tagRef := s!"refs/tags/{pin.version}" ++ "^{commit}"
    let tagOut ← gitIn dir #["rev-parse", "--verify", "--quiet", "--end-of-options", tagRef]
    unless tagOut.exitCode == 0 do
      throw <| IO.userError s!"REGULA: git rev-parse {pin.version} failed in {dir}:\n{tagOut.stderr}"
    let actualTag := tagOut.stdout.trimAscii.toString
    unless actualTag == pin.commit do
      throw <| IO.userError s!"REGULA: tag {pin.version} in {dir} resolves to {actualTag.quote}, expected {pin.commit.quote}"
  let statusArgs := if checkIgnored then
    #["status", "--porcelain=v1", "-z", "--untracked-files=all", "--ignored"]
  else
    #["status", "--porcelain=v1", "-z", "--untracked-files=all"]
  let statusOut ← gitIn dir statusArgs
  unless statusOut.exitCode == 0 do
    throw <| IO.userError s!"REGULA: git status failed in {dir}:\n{statusOut.stderr}"
  unless statusOut.stdout.isEmpty do
    throw <| IO.userError s!"REGULA: checkout {dir} has uncommitted, untracked, or ignored files"

def stageRegulaCheckout (pin : RegulaPin) : IO System.FilePath := do
  ensureDirChain "REGULA" regulaBasePrefixes
  let cacheDir := regulaCacheDirPath pin.commit
  let mk ← IO.Process.output { cmd := "mktemp", args := #["-d", ".lake/cache/regula/regula.tmp.XXXXXX"] }
  unless mk.exitCode == 0 do
    throw <| IO.userError s!"REGULA: mktemp -d failed in .lake/cache/regula:\n{mk.stderr}"
  let tmpRaw := mk.stdout.trimAscii.toString
  let expectedPrefix := ".lake/cache/regula/regula.tmp."
  unless tmpRaw.startsWith expectedPrefix && (tmpRaw.splitOn "/").length == 4 do
    throw <| IO.userError s!"REGULA: mktemp -d returned unexpected staging path {tmpRaw.quote}"
  let tmpPath := System.FilePath.mk tmpRaw
  try
    let tmpInfo ← try tmpPath.symlinkMetadata catch _ =>
      throw <| IO.userError s!"REGULA: staging directory {tmpPath} cannot be inspected"
    unless tmpInfo.type == .dir do
      throw <| IO.userError s!"REGULA: staging path {tmpPath} is not a real directory"
    let initOut ← gitIn tmpPath #["init", "--quiet"]
    unless initOut.exitCode == 0 do
      throw <| IO.userError s!"REGULA: git init failed in {tmpPath}:\n{initOut.stderr}"
    let refspec := s!"refs/tags/{pin.version}:refs/tags/{pin.version}"
    let fetchOut ← gitIn tmpPath #["fetch", "--quiet", "--depth", "1", "--no-tags", "--", regulaRepoUrl, refspec]
    unless fetchOut.exitCode == 0 do
      throw <| IO.userError s!"REGULA: failed to fetch {pin.version} from {regulaRepoUrl} (set REGULA_DIR for offline reuse):\n{fetchOut.stderr}"
    let tagRef := s!"refs/tags/{pin.version}" ++ "^{commit}"
    let tagOut ← gitIn tmpPath #["rev-parse", "--verify", "--quiet", "--end-of-options", tagRef]
    unless tagOut.exitCode == 0 && tagOut.stdout.trimAscii.toString == pin.commit do
      throw <| IO.userError s!"REGULA: fetched tag {pin.version} does not match pinned commit {pin.commit}"
    let coOut ← gitIn tmpPath #["checkout", "--quiet", "--detach", pin.commit]
    unless coOut.exitCode == 0 do
      throw <| IO.userError s!"REGULA: git checkout {pin.commit} failed in {tmpPath}:\n{coOut.stderr}"
    verifyRegulaCheckout pin tmpPath true true
    checkDirChain "REGULA" regulaBasePrefixes
    let preRename? ← try
      some <$> cacheDir.symlinkMetadata
    catch
      | .noFileOrDirectory .. => pure none
      | e => throw e
    match preRename? with
    | some info =>
      unless info.type == .dir do
        throw <| IO.userError s!"REGULA: cache path {cacheDir} is not a real directory (symlinks are rejected)"
      verifyRegulaCheckout pin cacheDir true true
      return cacheDir
    | none =>
      try
        IO.FS.rename tmpPath cacheDir
      catch e =>
        let raced? ← try
          some <$> cacheDir.symlinkMetadata
        catch
          | .noFileOrDirectory .. => pure none
          | _ => pure none
        match raced? with
        | some info =>
          unless info.type == .dir do
            throw <| IO.userError s!"REGULA: cache path {cacheDir} is not a real directory (symlinks are rejected)"
          verifyRegulaCheckout pin cacheDir true true
          return cacheDir
        | none =>
          throw <| IO.userError s!"REGULA: failed to stage {cacheDir}: {e}"
      checkDirChain "REGULA" (regulaCachePrefixes pin.commit)
      verifyRegulaCheckout pin cacheDir true true
      return cacheDir
  finally
    try
      IO.FS.removeDirAll tmpPath
    catch _ => pure ()

def ensureRegulaDir (pin : RegulaPin) : IO System.FilePath := do
  match ← IO.getEnv "REGULA_DIR" with
  | some raw =>
    let dir ← checkNoSymlinkDir "REGULA" "REGULA_DIR" raw
    verifyRegulaCheckout pin dir false false
    return dir
  | none =>
    if ← verifyExistingDirChain "REGULA" (regulaCachePrefixes pin.commit) then
      let cacheDir := regulaCacheDirPath pin.commit
      verifyRegulaCheckout pin cacheDir true true
      return cacheDir
    stageRegulaCheckout pin

def regulaEnv (proofDir : String) : Array (String × Option String) :=
  #[("REGULA_PROOF", some proofDir), ("REGULA_FULL", none),
    ("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LEAN_GITHASH", none),
    ("LAKE_CACHE_DIR", some ""), ("LAKE_NO_CACHE", some "true"),
    ("LAKE_ARTIFACT_CACHE", some "false"), ("LAKE_RESTORE_ARTIFACTS", some "false"),
    ("LAKE_CONFIG", some ""), ("LAKE_CACHE_KEY", none),
    ("LAKE_CACHE_ARTIFACT_ENDPOINT", none), ("LAKE_CACHE_REVISION_ENDPOINT", none),
    ("LAKE_CACHE_SERVICE", none), ("LAKE_PKG_URL_MAP", none)]

def splitNonEmptyLines (raw : String) : Array String :=
  (((raw.splitOn "\n").map (·.trimAscii.toString)).filter (· ≠ "")).toArray

inductive WalkItemKind where
  | dir
  | file (size : UInt64)
  | symlink
  | other
  deriving BEq

structure WalkItem where
  relPath : String
  kind : WalkItemKind

partial def walkDirEntries (root : System.FilePath) (skipTopGit : Bool) : IO (Array WalkItem) := do
  let rec go (curRel : String) (acc : Array WalkItem) : IO (Array WalkItem) := do
    let dirPath := if curRel.isEmpty then root else root / curRel
    let rawEntries ← dirPath.readDir
    let entries := rawEntries.qsort (fun a b => a.fileName < b.fileName)
    let mut out := acc
    for ent in entries do
      let name := ent.fileName
      if skipTopGit && curRel.isEmpty && name == ".git" then
        continue
      let rel := if curRel.isEmpty then name else s!"{curRel}/{name}"
      let finfo ← (root / rel).symlinkMetadata
      match finfo.type with
      | .dir =>
        out := out.push { relPath := rel, kind := .dir }
        out ← go rel out
      | .file =>
        out := out.push { relPath := rel, kind := .file finfo.byteSize }
      | .symlink =>
        out := out.push { relPath := rel, kind := .symlink }
      | .other =>
        out := out.push { relPath := rel, kind := .other }
    return out
  go "" #[]

def checkExtractedRegulaTree (dir : System.FilePath) : IO Unit := do
  checkRegularChildFile "REGULA" dir "lakefile.toml"
  checkRegularChildFile "REGULA" dir "lean-toolchain"
  checkAbsentPath "REGULA" dir "lakefile.lean"
  for item in ← walkDirEntries dir false do
    unless item.kind matches .dir | .file _ do
      throw <| IO.userError s!"REGULA: extracted checkout entry {dir / item.relPath} is not a regular file or directory"

inductive SnapshotEntry where
  | dir (relPath : String)
  | fileDigest (relPath : String) (size : UInt64) (sha256 : String)
  | fileBytes (relPath : String) (bytes : ByteArray)
  | symlink (relPath : String) (target : String)
  | other (relPath : String)
  deriving BEq

structure WorkspaceSnapshot where
  status : String
  stage : String
  workDiff : String
  indexDiff : String
  refs : String
  headCode : UInt32
  headOut : String
  entries : Array SnapshotEntry
  deriving BEq

def isBatchHashablePath (relPath : String) : Bool :=
  !relPath.contains '\n' && !relPath.contains '\r' && !relPath.contains '\\'

def snapshotWorkspace : IO WorkspaceSnapshot := do
  let status ← git #["status", "--porcelain=v1", "-z", "--untracked-files=all", "--ignored"]
  let stage ← git #["ls-files", "--stage", "-z"]
  let workDiff ← git #["diff", "--no-color", "--binary"]
  let indexDiff ← git #["diff", "--cached", "--no-color", "--binary"]
  let refs ← git #["for-each-ref", "--format=%(refname) %(objectname)"]
  let headRes ← IO.Process.output { cmd := "git", args := #["rev-parse", "--verify", "--quiet", "HEAD"] }
  let items ← walkDirEntries "." true
  let mut batchIndices : Array Nat := #[]
  let mut batchPaths : Array String := #[]
  for h : idx in [:items.size] do
    let item := items[idx]
    if let .file _ := item.kind then
      if isBatchHashablePath item.relPath then
        batchIndices := batchIndices.push idx
        batchPaths := batchPaths.push ("./" ++ item.relPath)
  let mut digests : Std.HashMap Nat String := {}
  let mut pos := 0
  while pos < batchPaths.size do
    let stop := min (pos + 200) batchPaths.size
    let chunkPaths := batchPaths.extract pos stop
    let chunkDigests ← sha256Batch "REGULA" chunkPaths
    for j in [:chunkPaths.size] do
      digests := digests.insert batchIndices[pos + j]! chunkDigests[j]!
    pos := stop
  let mut entries : Array SnapshotEntry := #[]
  for h : idx in [:items.size] do
    let item := items[idx]
    match item.kind with
    | .dir => entries := entries.push (.dir item.relPath)
    | .other => entries := entries.push (.other item.relPath)
    | .symlink =>
      let rl ← IO.Process.output { cmd := "readlink", args := #["--", "./" ++ item.relPath] }
      unless rl.exitCode == 0 do
        throw <| IO.userError s!"REGULA: readlink failed on {item.relPath}:\n{rl.stderr}"
      entries := entries.push (.symlink item.relPath rl.stdout)
    | .file size =>
      match digests.get? idx with
      | some digest => entries := entries.push (.fileDigest item.relPath size digest)
      | none => entries := entries.push (.fileBytes item.relPath (← IO.FS.readBinFile item.relPath))
  return { status, stage, workDiff, indexDiff, refs, headCode := headRes.exitCode, headOut := headRes.stdout, entries }

def parseStrictNat (s : String) : Option Nat :=
  if !s.isEmpty && s.all (fun c => '0' ≤ c && c ≤ '9') then s.toNat? else none

def parseRegulaCoverageLine (line : String) : Option (Nat × Nat) := do
  let body ← (line.dropPrefix? "  regula: read ").map (·.toString)
  let rest ← (body.dropSuffix? " of their constants").map (·.toString)
  match rest.splitOn " claimed modules and " with
  | [modsStr, declsStr] =>
    let nMods ← parseStrictNat modsStr
    let nDecls ← parseStrictNat declsStr
    return (nMods, nDecls)
  | _ => none

structure CanonicalPosixPath where
  path : System.FilePath
  abs : path.toString.startsWith "/" = true

def pathSegments (p : System.FilePath) : List String :=
  (p.toString.splitOn "/").filter (· ≠ "")

def isSameOrSubpath (root target : CanonicalPosixPath) : Bool :=
  (pathSegments root.path).isPrefixOf (pathSegments target.path)

theorem isSameOrSubpath_eq_true_iff (root target : CanonicalPosixPath) :
    isSameOrSubpath root target = true ↔
      ∃ rest, pathSegments target.path = pathSegments root.path ++ rest := by
  unfold isSameOrSubpath
  exact List.isPrefixOf_iff_prefix.trans
    ⟨fun ⟨rest, h⟩ => ⟨rest, h.symm⟩, fun ⟨rest, h⟩ => ⟨rest, h.symm⟩⟩

def CanonicalPosixPath.ofRealPath (rule label : String) (raw : System.FilePath) (checkSymlinks : Bool) :
    IO CanonicalPosixPath := do
  let real ← IO.FS.realPath raw
  let s := real.toString
  if s.contains '\n' || s.contains '\r' || s.contains '\x00' then
    throw <| IO.userError s!"{rule}: resolved {label} {s.quote} contains control characters"
  if (pathSegments real).any (fun seg => seg == "." || seg == "..") then
    throw <| IO.userError s!"{rule}: resolved {label} {s.quote} contains relative segments"
  if checkSymlinks then
    discard <| checkNoSymlinkDir rule label s
  if h : s.startsWith "/" then
    return ⟨real, h⟩
  else
    throw <| IO.userError s!"{rule}: resolved {label} {s.quote} is not an absolute POSIX path"

def resolveScratchParent : IO System.FilePath := do
  for var in ["TMPDIR", "TMP", "TEMP", "TEMPDIR"] do
    if let some raw ← IO.getEnv var then
      if raw.isEmpty then
        throw <| IO.userError s!"REGULA: {var} is set to an empty scratch directory path"
      return System.FilePath.mk raw
  return System.FilePath.mk "/tmp"

def checkRegula (mods : Array Name) : IO (Array Rejection) := do
  if let some err ← checkCommittedRegularFile regulaPinFile then
    return #[{ rule := "REGULA", message := err }]
  let pin ← readRegulaPin
  let regulaDir ← ensureRegulaDir pin
  let pkg ← CanonicalPosixPath.ofRealPath "REGULA" "resolved package directory" "." false
  let pkgRealStr := pkg.path.toString
  let scratchParent ← CanonicalPosixPath.ofRealPath "REGULA" "scratch parent directory"
    (← resolveScratchParent) true
  if isSameOrSubpath pkg scratchParent then
    throw <| IO.userError
      s!"REGULA: scratch parent directory {scratchParent.path.toString.quote} overlaps target workspace {pkgRealStr.quote}"
  let rawTmpBase ← IO.FS.createTempDir
  let (preSnap, out, postSnap) ←
    try
      let tmpBase ← CanonicalPosixPath.ofRealPath "REGULA" "temporary build directory" rawTmpBase true
      unless tmpBase.path.parent == some scratchParent.path do
        throw <| IO.userError
          s!"REGULA: temporary build directory {tmpBase.path.toString.quote} is not under scratch parent {scratchParent.path.toString.quote}"
      if isSameOrSubpath pkg tmpBase || isSameOrSubpath tmpBase pkg then
        throw <| IO.userError
          s!"REGULA: temporary build directory {tmpBase.path.toString.quote} overlaps target workspace {pkgRealStr.quote}"
      let tarPath := tmpBase.path / "regula.tar"
      let srcDir := tmpBase.path / "src"
      IO.FS.createDir srcDir
      let archOut ← gitIn regulaDir #["archive", "--format=tar", s!"--output={tarPath}", pin.commit]
      unless archOut.exitCode == 0 do
        throw <| IO.userError s!"REGULA: git archive failed in {regulaDir}:\n{archOut.stderr}"
      let tarOut ← IO.Process.output { cmd := "tar", args := #["-xf", tarPath.toString, "-C", srcDir.toString] }
      unless tarOut.exitCode == 0 do
        throw <| IO.userError s!"REGULA: tar extraction failed in {srcDir}:\n{tarOut.stderr}"
      IO.FS.removeFile tarPath
      checkExtractedRegulaTree srcDir
      let preSnap ← snapshotWorkspace
      let out ← IO.Process.output {
        cmd := "lake"
        args := #["exe", "lint", regulaProfile]
        cwd := some srcDir
        env := regulaEnv pkgRealStr
      }
      let postSnap ← snapshotWorkspace
      pure (preSnap, out, postSnap)
    finally
      try
        IO.FS.removeDirAll rawTmpBase
      catch _ => pure ()
  if preSnap != postSnap then
    return #[{ rule := "REGULA", message := "Regula mutated the lean-intent workspace during proof-verdict checking" }]
  let expectedVerdict :=
    s!"regula: proof verdict: pass, which says nothing about what ran during the build, on {pkgRealStr}"
  if out.exitCode == 0 then
    if out.stdout.endsWith "\n" then
      match (out.stdout.splitOn "\n").reverse with
      | "" :: lastLine :: secondLastLine :: _ =>
        if lastLine == expectedVerdict then
          match parseRegulaCoverageLine secondLastLine with
          | some (readMods, readDecls) =>
            if readMods == mods.size && readDecls > 0 then
              return #[]
            return #[{ rule := "REGULA", message :=
              s!"Regula covered {readMods} modules ({readDecls} constants), expected {mods.size} modules and > 0 constants" }]
          | none =>
            return #[{ rule := "REGULA", message :=
              s!"Regula exited 0 without expected module coverage line before verdict; stdout:\n{out.stdout}" }]
        return #[{ rule := "REGULA", message :=
          s!"Regula exited 0 without expected exact final verdict {expectedVerdict.quote}; stdout:\n{out.stdout}" }]
      | _ =>
        return #[{ rule := "REGULA", message :=
          s!"Regula exited 0 with incomplete stdout:\n{out.stdout}" }]
    return #[{ rule := "REGULA", message :=
      s!"Regula exited 0 without trailing newline after verdict; stdout:\n{out.stdout}" }]
  let lines := splitNonEmptyLines (out.stdout ++ "\n" ++ out.stderr)
  if lines.isEmpty then
    return #[{ rule := "REGULA", message := s!"Regula exited with status {out.exitCode}" }]
  return lines.map fun l => { rule := "REGULA", message := l }

def check (opts : CheckOpts) : IO (Array Rejection) := do
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
  let allFiles ← trackedLeanFiles
  let notModules ← checkModuleFiles allFiles
  unless notModules.isEmpty do
    return notModules
  let built ← build files
  unless built.isEmpty do
    return built
  let codes ← checkCodes pkg.leanLibDir mods
  let commentErrs ← checkComments opts
  let regulaErrs ← checkRegula mods
  initSearchPath (← findSysroot) [pkg.leanLibDir]
  let env ← importModules ((mods.map fun m => { module := m }).push { module := `Std.Internal.UV.System }) {}
  let idxs := mods.filterMap env.getModuleIdx?
  let mut errs : Array Rejection := #[]
  let mut audited := 0
  let mut compiled : Array Name := #[]
  for (c, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? c then
      if idxs.contains idx then
        audited := audited + 1
        errs := errs ++ (← auditConstant env env.header.modules[idx.toNat]!.module c ci)
        if (IR.findEnvDecl env c).isSome then
          compiled := compiled.push c
  if audited == 0 then
    errs := errs.push { rule := "AXIOMS", message := "the library's modules declare no constant" }
  return errs ++ checkProcess env compiled ++ codes ++ commentErrs ++ regulaErrs

def checkUsage : String :=
  "usage: lean --run tools/check.lean [--base-ref <ref>] | --tests | --tests-module <file> <out> | --comments [<file>]"

def parseCheckArgs (args : List String) : Except String CheckOpts :=
  go args {}
where
  go (rest : List String) (opts : CheckOpts) : Except String CheckOpts := do
    match rest with
    | [] => return opts
    | "--base-ref" :: ref :: tl =>
      if opts.baseRef?.isSome then
        throw "duplicate --base-ref option"
      go tl { opts with baseRef? := some (← BaseRef.parse ref) }
    | ["--base-ref"] =>
      throw "missing value after --base-ref"
    | arg :: _ =>
      throw s!"unknown option or argument {arg.quote}\n{checkUsage}"

end Check

public unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["--tests"] =>
    for t in ← Check.projectTests do
      IO.println t
    return 0
  | ["--tests-module", file, out] =>
    Check.moduleTests file out
    return 0
  | ["--comments"] =>
    Check.listComments none
    return 0
  | ["--comments", file] =>
    Check.listComments (some file)
    return 0
  | _ =>
    let opts ← match Check.parseCheckArgs args with
      | .ok o => pure o
      | .error e => throw <| IO.userError e
    let errs ← Check.check opts
    for e in errs do
      IO.println s!"[{e.rule}] {e.message}"
    return if errs.isEmpty then 0 else 1
