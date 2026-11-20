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

def ratchetFile : String := "tools/comment-ratchet.json"

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

def libraryFiles : IO (Array String) :=
  return (← trackedLeanFiles).filter (!·.startsWith "tools/")

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

def testsLean : String := "4.35.0"

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

structure CommentSpan where
  startByte : Nat
  stopByte : Nat
  kind : String
  startLine : Nat
  endLine : Nat

structure CommentAcc where
  spans : Std.HashMap Nat CommentSpan := {}

def recordSpan (fileMap : FileMap) (kind : String) (startPos stopPos : String.Pos.Raw)
    (acc : CommentAcc) : Except String CommentAcc :=
  let sb := startPos.byteIdx
  let eb := stopPos.byteIdx
  match acc.spans.get? sb with
  | some prev =>
    if prev.stopByte == eb && prev.kind == kind then .ok acc
    else .error s!"inconsistent overlapping comment span at byte {sb}"
  | none =>
    let lastPos := if eb > sb then String.Pos.Raw.prev fileMap.source stopPos else stopPos
    let sl := (fileMap.toPosition startPos).line
    let el := (fileMap.toPosition lastPos).line
    .ok { spans := acc.spans.insert sb { startByte := sb, stopByte := eb, kind, startLine := sl, endLine := el } }

partial def scanTrivia (fileMap : FileMap) (sub : Substring.Raw) (acc : CommentAcc) :
    Except String CommentAcc :=
  go sub.startPos acc
where
  finishBlock (nesting : Nat) (pos : String.Pos.Raw) : Except String String.Pos.Raw :=
    if pos ≥ sub.stopPos then
      .error "unterminated block comment in Lean parser trivia"
    else
      let c := String.Pos.Raw.get sub.str pos
      let next := String.Pos.Raw.next sub.str pos
      if c == '-' && next < sub.stopPos && String.Pos.Raw.get sub.str next == '/' then
        let after := String.Pos.Raw.next sub.str next
        if nesting == 1 then .ok after
        else finishBlock (nesting - 1) after
      else if c == '/' && next < sub.stopPos && String.Pos.Raw.get sub.str next == '-' then
        finishBlock (nesting + 1) (String.Pos.Raw.next sub.str next)
      else
        finishBlock nesting next
  go (pos : String.Pos.Raw) (acc : CommentAcc) : Except String CommentAcc :=
    if pos ≥ sub.stopPos then
      .ok acc
    else
      let c := String.Pos.Raw.get sub.str pos
      let next := String.Pos.Raw.next sub.str pos
      if c.isWhitespace then
        go next acc
      else if c == '-' && next < sub.stopPos && String.Pos.Raw.get sub.str next == '-' then
        let rec toEol (p : String.Pos.Raw) : String.Pos.Raw :=
          if p ≥ sub.stopPos then p
          else if String.Pos.Raw.get sub.str p == '\n' then p
          else toEol (String.Pos.Raw.next sub.str p)
        let eol := toEol (String.Pos.Raw.next sub.str next)
        match recordSpan fileMap "line" pos eol acc with
        | .ok acc' => go eol acc'
        | .error e => .error e
      else if c == '/' && next < sub.stopPos && String.Pos.Raw.get sub.str next == '-' then
        let afterOpen := String.Pos.Raw.next sub.str next
        if afterOpen ≥ sub.stopPos then
          .error "unterminated block comment in Lean parser trivia"
        else
          let third := String.Pos.Raw.get sub.str afterOpen
          if third == '-' || third == '!' then
            .error "unexpected doc comment opener in Lean parser trivia"
          else
            match finishBlock 1 (String.Pos.Raw.next sub.str afterOpen) with
            | .error e => .error e
            | .ok endPos =>
              match recordSpan fileMap "block" pos endPos acc with
              | .ok acc' => go endPos acc'
              | .error e => .error e
      else
        .error s!"unexpected non-whitespace character {repr c} at byte {pos.byteIdx} in Lean parser trivia"

def checkSlice (fileMap : FileMap) (input : String) (startPos stopPos : String.Pos.Raw)
    (acc : CommentAcc) : Except String CommentAcc :=
  if startPos < stopPos then
    scanTrivia fileMap ⟨input, startPos, stopPos⟩ acc
  else
    .ok acc

def checkLeading (fileMap : FileMap) (info : SourceInfo) (acc : CommentAcc) :
    Except String CommentAcc :=
  match info with
  | .original leading _ _ _ =>
    if leading.startPos < leading.stopPos then scanTrivia fileMap leading acc else .ok acc
  | _ => .ok acc

def checkTrailing (fileMap : FileMap) (info : SourceInfo) (acc : CommentAcc) :
    Except String CommentAcc :=
  match info with
  | .original _ _ trailing _ =>
    if trailing.startPos < trailing.stopPos then scanTrivia fileMap trailing acc else .ok acc
  | _ => .ok acc

def checkInfo (fileMap : FileMap) (info : SourceInfo) (acc : CommentAcc) :
    Except String CommentAcc := do
  let acc ← checkLeading fileMap info acc
  checkTrailing fileMap info acc

partial def walkSyntax (fileMap : FileMap) (stx : Syntax) (acc : CommentAcc) :
    Except String CommentAcc := do
  match stx with
  | .missing => return acc
  | .atom info _ => checkInfo fileMap info acc
  | .ident info _ _ _ => checkInfo fileMap info acc
  | .node info k args =>
    let acc ← checkInfo fileMap info acc
    if k == ``Parser.Command.docComment || k == ``Parser.Command.plainDocComment ||
       k == ``Parser.Command.moduleDoc then
      let kind := if k == ``Parser.Command.moduleDoc then "moddoc" else "doc"
      let acc ← match stx.getPos?, stx.getTailPos? with
        | some s, some e => recordSpan fileMap kind s e acc
        | _, _ => .error s!"{kind} node has no source position"
      let acc ← match stx.getHeadInfo? with
        | some head => checkLeading fileMap head acc
        | none => .ok acc
      match stx.getTailInfo? with
      | some tail => checkTrailing fileMap tail acc
      | none => .ok acc
    else
      args.foldlM (fun acc arg => walkSyntax fileMap arg acc) acc

def collectCommand (file : String) (fileMap : FileMap) (input : String)
    (prevPos nextPos : String.Pos.Raw) (stx : Syntax) (acc : CommentAcc) : IO CommentAcc := do
  if stx.isOfKind ``Parser.Command.exit then
    throw <| IO.userError s!"{file}: `#exit` is not allowed when checking comments"
  let step : Except String CommentAcc := do
    let acc ← match stx.getPos? with
      | some cpos => checkSlice fileMap input prevPos cpos acc
      | none => .ok acc
    let acc ← walkSyntax fileMap stx acc
    match stx.getTailPos? with
    | some cend => checkSlice fileMap input cend nextPos acc
    | none => .ok acc
  match step with
  | .ok a => return a
  | .error e => throw <| IO.userError s!"{file}: {e}"

inductive FastParseOutcome where
  | ok (spans : Array CommentSpan)
  | needsFrontend
  | failed (msg : String)

def sortedSpans (acc : CommentAcc) : Array CommentSpan :=
  (acc.spans.toList.map (·.2)).toArray.qsort fun a b => a.startByte < b.startByte

def distinctCommentLines (spans : Array CommentSpan) : Nat := Id.run do
  let mut ls : Std.HashSet Nat := {}
  for sp in spans do
    for l in [sp.startLine : sp.endLine + 1] do
      ls := ls.insert l
  return ls.size

def parseCommentsFast (env : Environment) (file : String) : IO FastParseOutcome := do
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let (header, mps, messages) ← Parser.parseHeader inputCtx
  if messages.hasErrors then
    let shown ← messages.toList.mapM (·.toString)
    return .failed s!"{file}: Lean's parser could not read its header:\n{String.join shown}"
  let mut acc : CommentAcc := {}
  let headerStep : Except String CommentAcc := do
    match header.raw.getPos? with
    | some hpos =>
      let acc ← checkSlice inputCtx.fileMap input ⟨0⟩ hpos acc
      let acc ← walkSyntax inputCtx.fileMap header.raw acc
      match header.raw.getTailPos? with
      | some hend => checkSlice inputCtx.fileMap input hend mps.pos acc
      | none => .ok acc
    | none =>
      checkSlice inputCtx.fileMap input ⟨0⟩ mps.pos acc
  match headerStep with
  | .ok a => acc := a
  | .error e => return .failed s!"{file}: {e}"
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  let mut mps := mps
  let mut messages := messages
  repeat
    let prevPos := mps.pos
    let (stx, mps', messages') := Parser.parseCommand inputCtx pmctx mps messages
    if messages'.hasErrors then
      return .needsFrontend
    mps := mps'
    messages := messages'
    if stx.isOfKind ``Parser.Command.eoi then
      let eoiStep : Except String CommentAcc := do
        let acc ← walkSyntax inputCtx.fileMap stx acc
        checkSlice inputCtx.fileMap input prevPos inputCtx.inputString.rawEndPos acc
      match eoiStep with
      | .ok a => acc := a
      | .error e => return .failed s!"{file}: {e}"
      break
    try
      acc ← collectCommand file inputCtx.fileMap input prevPos mps.pos stx acc
    catch e =>
      return .failed (toString e)
  unless mps.pos == inputCtx.inputString.rawEndPos do
    return .failed s!"{file}: parser stopped at byte {mps.pos.byteIdx} before EOF {inputCtx.inputString.rawEndPos.byteIdx}"
  return .ok (sortedSpans acc)

unsafe def parseCommentsViaFrontend (file : String) (mod : Name) : IO (Array CommentSpan) := do
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let opts := (({} : Options).setBool `Elab.async false).setBool `debug.byAsSorry true
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  if messages.hasErrors then
    let shown ← messages.toList.mapM (·.toString)
    throw <| IO.userError s!"{file}: Lean's parser could not read its header:\n{String.join shown}"
  enableInitializersExecution
  let (env, messages) ← Elab.processHeader header opts messages inputCtx (mainModule := mod)
  if messages.hasErrors then
    let shown ← messages.toList.mapM (·.toString)
    throw <| IO.userError s!"{file}: Lean could not process its header:\n{String.join shown}"
  let state := Elab.Command.mkState env messages opts
  let s ← Elab.IO.processCommandsIncrementally inputCtx parserState state none
  if s.commandState.messages.hasErrors then
    let shown ← s.commandState.messages.toList.mapM (·.toString)
    throw <| IO.userError s!"{file}: Lean could not parse or elaborate it:\n{String.join shown}"
  let mut acc : CommentAcc := {}
  let headerStep : Except String CommentAcc := do
    match header.raw.getPos? with
    | some hpos =>
      let acc ← checkSlice inputCtx.fileMap input ⟨0⟩ hpos acc
      let acc ← walkSyntax inputCtx.fileMap header.raw acc
      match header.raw.getTailPos? with
      | some hend => checkSlice inputCtx.fileMap input hend parserState.pos acc
      | none => .ok acc
    | none =>
      checkSlice inputCtx.fileMap input ⟨0⟩ parserState.pos acc
  match headerStep with
  | .ok a => acc := a
  | .error e => throw <| IO.userError s!"{file}: {e}"
  let mut snap := s.initialSnap
  let mut prevPos := parserState.pos
  repeat
    let cmd := snap.stx
    let nextPos := snap.parserState.pos
    if cmd.isOfKind ``Parser.Command.eoi then
      let eoiStep : Except String CommentAcc := do
        let acc ← walkSyntax inputCtx.fileMap cmd acc
        checkSlice inputCtx.fileMap input prevPos inputCtx.inputString.rawEndPos acc
      match eoiStep with
      | .ok a => acc := a
      | .error e => throw <| IO.userError s!"{file}: {e}"
      prevPos := nextPos
      break
    acc ← collectCommand file inputCtx.fileMap input prevPos nextPos cmd acc
    prevPos := nextPos
    match snap.nextCmdSnap? with
    | some next => snap := next.get
    | none => break
  unless prevPos == inputCtx.inputString.rawEndPos do
    throw <| IO.userError s!"{file}: frontend stopped at byte {prevPos.byteIdx} before EOF {inputCtx.inputString.rawEndPos.byteIdx}"
  return sortedSpans acc

unsafe def fileCommentSpans (env : Environment) (file : String) (mod : Name) :
    IO (Array CommentSpan) := do
  match ← parseCommentsFast env file with
  | .ok spans => return spans
  | .failed msg => throw <| IO.userError msg
  | .needsFrontend => parseCommentsViaFrontend file mod

def parsePosNat (j : Json) (ctx : String) : IO Nat := do
  match j with
  | .num n =>
    if n.exponent == 0 && n.mantissa > 0 then
      return n.mantissa.toNat
    throw <| IO.userError s!"{ctx}: expected a positive integer, got {j}"
  | _ => throw <| IO.userError s!"{ctx}: expected a positive integer, got {j}"

def loadRatchet : IO (Std.HashMap String (Nat × Nat)) := do
  let raw ← IO.FS.readFile ratchetFile
  let json ← match Json.parse raw with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"{ratchetFile}: invalid JSON: {e}"
  let .arr entries := json
    | throw <| IO.userError s!"{ratchetFile}: top-level JSON value must be an array"
  let mut map : Std.HashMap String (Nat × Nat) := {}
  for idx in [0 : entries.size] do
    let entry := entries[idx]!
    let .obj kvs := entry
      | throw <| IO.userError s!"{ratchetFile}[{idx}]: entry must be a JSON object"
    let keys := kvs.toList.map (·.1)
    unless keys.length == 3 && keys.contains "file" && keys.contains "comments" && keys.contains "lines" do
      throw <| IO.userError s!"{ratchetFile}[{idx}]: entry must have exact keys file, comments, lines"
    let some (.str file) := kvs.get? "file"
      | throw <| IO.userError s!"{ratchetFile}[{idx}]: file must be a string"
    if file.isEmpty then
      throw <| IO.userError s!"{ratchetFile}[{idx}]: file must not be empty"
    if map.contains file then
      throw <| IO.userError s!"{ratchetFile}[{idx}]: duplicate entry for {file}"
    let some cJson := kvs.get? "comments"
      | throw <| IO.userError s!"{ratchetFile}[{idx}]: missing comments"
    let some lJson := kvs.get? "lines"
      | throw <| IO.userError s!"{ratchetFile}[{idx}]: missing lines"
    let comments ← parsePosNat cJson s!"{ratchetFile}[{idx}].comments ({file})"
    let lines ← parsePosNat lJson s!"{ratchetFile}[{idx}].lines ({file})"
    map := map.insert file (comments, lines)
  return map

unsafe def loadParserEnv (libDir : System.FilePath) (libMods : Array Name) : IO Environment := do
  initSearchPath (← findSysroot) [libDir]
  enableInitializersExecution
  importModules ((libMods ++ #[`Lean, `Lake]).map fun m => { module := m }) {} (loadExts := true)

unsafe def checkComments (libDir : System.FilePath) (libMods : Array Name)
    (allFiles : Array String) : IO (Array Rejection) := do
  let reject (message : String) : Rejection := { rule := "NO-COMMENTS", message }
  if allFiles.isEmpty then
    return #[reject "Git's index lists no Lean file"]
  let ratchet ← loadRatchet
  let mut errs : Array Rejection := #[]
  for (f, _) in ratchet.toList do
    unless allFiles.contains f do
      errs := errs.push (reject s!"{ratchetFile} lists {f}, which is not a tracked Lean file")
  let allMods ← moduleNames allFiles
  let env ← loadParserEnv libDir libMods
  for (f, m) in allFiles.zip allMods do
    let spans ← fileCommentSpans env f m
    let actualComments := spans.size
    let actualLines := distinctCommentLines spans
    match ratchet.get? f with
    | none =>
      if actualComments > 0 || actualLines > 0 then
        errs := errs.push (reject s!"{f} has {actualComments} comment(s) across {actualLines} line(s), and is not in {ratchetFile}")
    | some (maxComments, maxLines) =>
      if actualComments == 0 && actualLines == 0 then
        errs := errs.push (reject s!"{f} now has 0 comments; remove it from {ratchetFile} to lock in the ratchet")
      else if actualComments > maxComments || actualLines > maxLines then
        errs := errs.push (reject s!"{f} has {actualComments} comment(s) across {actualLines} line(s), exceeding its ratchet limit of {maxComments} comment(s) across {maxLines} line(s) in {ratchetFile}")
      else if actualComments < maxComments || actualLines < maxLines then
        errs := errs.push (reject s!"{f} now has {actualComments} comment(s) across {actualLines} line(s), below its ratchet limit of {maxComments} comment(s) across {maxLines} line(s); tighten {ratchetFile} to lock in the reduction")
  return errs

unsafe def listComments (target? : Option String) (asJson : Bool := false) : IO Unit := do
  let allFiles ← trackedLeanFiles
  if allFiles.isEmpty then
    throw <| IO.userError "the project tracks no Lean file"
  let pkg ← loadConfig
  let libFiles ← libraryFiles
  let libMods ← moduleNames libFiles
  let allMods ← moduleNames allFiles
  let env ← loadParserEnv pkg.leanLibDir libMods
  match target? with
  | some file =>
    let some mod := (allFiles.zip allMods).find? (·.1 == file) |>.map (·.2)
      | throw <| IO.userError s!"{file} is not a Lean file Git's index lists here"
    let spans ← fileCommentSpans env file mod
    let lines := distinctCommentLines spans
    IO.println s!"{file}: {spans.size} comment(s), {lines} line(s)"
    for sp in spans do
      IO.println s!"  {sp.kind} L{sp.startLine}-L{sp.endLine}"
  | none =>
    let mut rows : Array (String × Nat × Nat) := #[]
    let mut totComments := 0
    let mut totLines := 0
    for (f, m) in allFiles.zip allMods do
      let spans ← fileCommentSpans env f m
      let c := spans.size
      let l := distinctCommentLines spans
      if c > 0 then
        rows := rows.push (f, c, l)
        totComments := totComments + c
        totLines := totLines + l
    if asJson then
      IO.println "["
      for idx in [0 : rows.size] do
        let (f, c, l) := rows[idx]!
        let comma := if idx + 1 < rows.size then "," else ""
        IO.println s!"  \{\"file\": {Json.str f}, \"comments\": {c}, \"lines\": {l}}{comma}"
      IO.println "]"
    else
      for (f, c, l) in rows do
        IO.println s!"{f}: {c} comment(s), {l} line(s)"
      IO.println s!"total: {rows.size}/{allFiles.size} files with comments, {totComments} comment(s), {totLines} line(s)"

def checkCommentsSubprocess : IO (Array Rejection) := do
  let top := System.FilePath.mk (← git #["rev-parse", "--show-toplevel"]).trimAscii.toString
  let script := top / "tools" / "check.lean"
  let o ← IO.Process.output { cmd := "lean", args := #["--run", script.toString, "--check-comments"] }
  match o.exitCode with
  | 0 => return #[]
  | 1 =>
    let lines := ((o.stdout.splitOn "\n").filter (· ≠ "")).toArray
    if lines.isEmpty then
      return #[{ rule := "NO-COMMENTS", message :=
        s!"tools/check.lean --check-comments exited with status 1 and printed no reason; its standard error:\n{o.stderr}" }]
    return lines.map fun l => { rule := "NO-COMMENTS", message := l }
  | c => throw <| IO.userError s!"tools/check.lean --check-comments could not run (status {c}):\n{o.stdout}{o.stderr}"

unsafe def runCheckCommentsMain : IO UInt32 := do
  try
    let pkg ← loadConfig
    let libFiles ← libraryFiles
    let libMods ← moduleNames libFiles
    let allFiles ← trackedLeanFiles
    let errs ← checkComments pkg.leanLibDir libMods allFiles
    for e in errs do
      IO.println e.message
    return if errs.isEmpty then 0 else 1
  catch e =>
    try IO.eprintln s!"tools/check.lean --check-comments could not run: {e}" catch _ => pure ()
    return 2

def check : IO (Array Rejection) := do
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
  let commentErrs ← checkCommentsSubprocess
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
        errs := errs ++ (← auditConstant env env.header.moduleNames[idx.toNat]! c ci)
        if (IR.findEnvDecl env c).isSome then
          compiled := compiled.push c
  if audited == 0 then
    errs := errs.push { rule := "AXIOMS", message := "the library's modules declare no constant" }
  return errs ++ checkProcess env compiled ++ codes ++ commentErrs

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
  | ["--check-comments"] =>
    Check.runCheckCommentsMain
  | ["--comments"] =>
    Check.listComments none false
    return 0
  | ["--comments", file] =>
    Check.listComments (some file) false
    return 0
  | ["--comments-json"] =>
    Check.listComments none true
    return 0
  | [] =>
    let errs ← Check.check
    for e in errs do
      IO.println s!"[{e.rule}] {e.message}"
    return if errs.isEmpty then 0 else 1
  | _ => throw <| IO.userError "usage: lean --run tools/check.lean [--tests | --tests-module <file> <out> | --check-comments | --comments [<file>] | --comments-json]"
