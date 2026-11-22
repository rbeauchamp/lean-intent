module

import Lean
import Lake
import Lake.Load.Package
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
    kinds.contains m.getKind && m[1].isIdent && names.contains m[1].getId
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
   (``IO.getEnv, "lean_io_getenv")]

def processQueries : List String :=
  boundQueries.map (·.2) ++
    ["lean_uv_exepath", "lean_uv_cwd", "lean_uv_os_getenv", "lean_uv_os_environ",
     "lean_uv_os_homedir", "lean_uv_os_tmpdir", "lean_uv_os_get_passwd", "lean_uv_os_gethostname",
     "lean_uv_os_uname"]

def notFollowed : List Name := [`Lean.manualRoot]

def bindsTo (symbol : String) : ExternEntry → Bool
  | .standard _ fn => fn == symbol
  | .inline _ pattern => (pattern.splitOn symbol).length > 1
  | _ => false

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

def isSha256 (s : String) : Bool :=
  s.length == 64 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

def isValidReleaseTag (s : String) : Bool :=
  s.startsWith "v" && s.length > 1 && !s.contains ".." &&
    s.all fun c => c.isAlphanum || c == '.' || c == '-'

structure NoCommentsPin where
  version : String
  darwinArm64Sha256 : String
  linuxX86_64Sha256 : String

def parseNoCommentsPin (raw : String) : Except String NoCommentsPin := do
  if raw.contains '\r' then
    throw s!"{noCommentsPinFile}: expected LF line endings"
  let lines := if raw.endsWith "\n" then (raw.splitOn "\n").dropLast else raw.splitOn "\n"
  if lines.isEmpty then
    throw s!"{noCommentsPinFile}: file is empty"
  let mut version? : Option String := none
  let mut darwin? : Option String := none
  let mut linux? : Option String := none
  for line in lines do
    match line.splitOn "=" with
    | [k, v] =>
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
    | _ =>
      throw s!"{noCommentsPinFile}: expected KEY=VALUE line, got {line.quote}"
  let some version := version?
    | throw s!"{noCommentsPinFile}: missing VERSION"
  let some darwinArm64Sha256 := darwin?
    | throw s!"{noCommentsPinFile}: missing DARWIN_ARM64_SHA256"
  let some linuxX86_64Sha256 := linux?
    | throw s!"{noCommentsPinFile}: missing LINUX_X86_64_SHA256"
  return { version, darwinArm64Sha256, linuxX86_64Sha256 }

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

def sha256File (path : System.FilePath) : IO String := do
  let sha256sumRes? ← try
    some <$> IO.Process.output { cmd := "sha256sum", args := #["--", path.toString] }
  catch _ =>
    pure none
  match sha256sumRes? with
  | some o =>
    unless o.exitCode == 0 do
      throw <| IO.userError s!"NO-COMMENTS: sha256sum failed on {path}:\n{o.stderr}"
    parseSha256Output "sha256sum" o.stdout
  | none =>
    let o ← IO.Process.output { cmd := "shasum", args := #["-a", "256", "--", path.toString] }
    unless o.exitCode == 0 do
      throw <| IO.userError s!"NO-COMMENTS: shasum failed on {path}:\n{o.stderr}"
    parseSha256Output "shasum" o.stdout

def ensureNoCommentsBin (pin : NoCommentsPin) : IO System.FilePath := do
  let (assetName, expectedSha) ← platformAsset pin
  let envBin? := (← IO.getEnv "NO_COMMENTS_BIN").bind fun s =>
    let trimmed := s.trimAscii.toString
    if trimmed.isEmpty then none else some trimmed
  if let some raw := envBin? then
    let bin ← try IO.FS.realPath raw catch _ =>
      throw <| IO.userError s!"NO-COMMENTS: NO_COMMENTS_BIN ({raw}) does not exist or cannot be resolved"
    let info ← try bin.metadata catch _ =>
      throw <| IO.userError s!"NO-COMMENTS: NO_COMMENTS_BIN ({raw}) cannot be inspected"
    unless info.type == .file do
      throw <| IO.userError s!"NO-COMMENTS: NO_COMMENTS_BIN ({raw}) is not a regular file"
    let actual ← sha256File bin
    unless actual == expectedSha do
      throw <| IO.userError s!"NO-COMMENTS: NO_COMMENTS_BIN ({raw}) SHA-256 mismatch: expected {expectedSha}, got {actual}"
    return bin
  let cacheDir := System.FilePath.mk ".lake" / "cache" / "no-comments" / expectedSha
  let cacheBin := cacheDir / "no-comments"
  let existing? ← try some <$> cacheBin.symlinkMetadata catch _ => pure none
  if let some info := existing? then
    unless info.type == .file do
      throw <| IO.userError s!"NO-COMMENTS: cached binary path {cacheBin} is not a regular file"
    let actual ← sha256File cacheBin
    unless actual == expectedSha do
      throw <| IO.userError s!"NO-COMMENTS: cached binary {cacheBin} SHA-256 mismatch: expected {expectedSha}, got {actual}"
    return cacheBin
  IO.FS.createDirAll cacheDir
  let mk ← IO.Process.output { cmd := "mktemp", args := #[(cacheDir / "no-comments.tmp.XXXXXX").toString] }
  unless mk.exitCode == 0 do
    throw <| IO.userError s!"NO-COMMENTS: mktemp failed in {cacheDir}:\n{mk.stderr}"
  let tmpPath := System.FilePath.mk mk.stdout.trimAscii.toString
  try
    let url := s!"https://github.com/rbeauchamp/lean-no-comments/releases/download/{pin.version}/{assetName}"
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
    let actual ← sha256File tmpPath
    unless actual == expectedSha do
      throw <| IO.userError s!"NO-COMMENTS: downloaded {assetName} ({pin.version}) SHA-256 mismatch: expected {expectedSha}, got {actual}"
    IO.setAccessRights tmpPath {
      user := { read := true, write := true, execution := true }
      group := { read := true, execution := true }
      other := { read := true, execution := true }
    }
    IO.FS.rename tmpPath cacheBin
    let cachedActual ← sha256File cacheBin
    unless cachedActual == expectedSha do
      throw <| IO.userError s!"NO-COMMENTS: cached binary {cacheBin} SHA-256 mismatch after staging: expected {expectedSha}, got {cachedActual}"
    return cacheBin
  finally
    try
      if ← tmpPath.pathExists then
        IO.FS.removeFile tmpPath
    catch _ => pure ()

def checkComments (opts : CheckOpts) : IO (Array Rejection) := do
  if let some err ← checkWorkingTreeRegularFile noCommentsPinFile then
    return #[{ rule := "NO-COMMENTS", message := err }]
  if let some err ← checkWorkingTreeRegularFile noCommentsConfigFile then
    return #[{ rule := "NO-COMMENTS", message := err }]
  let pin ← readNoCommentsPin
  let bin ← ensureNoCommentsBin pin
  let mut args := #["check"]
  if let some ref := opts.baseRef? then
    args := args ++ #["--base-ref", ref.value]
  let out ← IO.Process.output { cmd := bin.toString, args }
  if out.exitCode == 0 then
    return #[]
  let raw := (out.stderr ++ "\n" ++ out.stdout).trimAscii.toString
  let lines := (((raw.splitOn "\n").map (·.trimAscii.toString)).filter (· ≠ "")).toArray
  if lines.isEmpty then
    return #[{ rule := "NO-COMMENTS", message := s!"{bin} check exited with status {out.exitCode}" }]
  return lines.map fun l => { rule := "NO-COMMENTS", message := l }

def listComments (target? : Option String) : IO Unit := do
  if let some err ← checkWorkingTreeRegularFile noCommentsPinFile then
    throw <| IO.userError s!"NO-COMMENTS: {err}"
  if let some err ← checkWorkingTreeRegularFile noCommentsConfigFile then
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
  initSearchPath (← findSysroot) [pkg.leanLibDir]
  let env ← importModules (mods.map fun m => { module := m }) {}
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
  return errs ++ checkProcess env compiled ++ codes ++ commentErrs

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
