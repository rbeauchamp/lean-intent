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

structure Comment where
  kind : String
  startLine : Nat
  endLine : Nat
  fingerprint : String

structure CommentAcc where
  spans : Std.HashMap Nat (Nat × Comment) := {}

def commentKinds : List String := ["line", "block", "doc", "moddoc"]

def fingerprint (text : String) : String :=
  let h := text.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211)
    (14695981039346656037 : UInt64)
  let digits := Nat.toDigits 16 h.toNat
  String.ofList (List.replicate (16 - digits.length) '0' ++ digits)

def isFingerprint (s : String) : Bool :=
  s.length == 16 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

def recordSpan (fileMap : FileMap) (kind : String) (startPos stopPos : String.Pos.Raw)
    (acc : CommentAcc) : Except String CommentAcc :=
  let sb := startPos.byteIdx
  let eb := stopPos.byteIdx
  match acc.spans.get? sb with
  | some (prevStop, prev) =>
    if prevStop == eb && prev.kind == kind then .ok acc
    else .error s!"inconsistent overlapping comment span at byte {sb}"
  | none =>
    let lastPos := if eb > sb then String.Pos.Raw.prev fileMap.source stopPos else stopPos
    let text := (⟨fileMap.source, startPos, stopPos⟩ : Substring.Raw).toString
    .ok { spans := acc.spans.insert sb (eb,
      { kind, startLine := (fileMap.toPosition startPos).line,
        endLine := (fileMap.toPosition lastPos).line, fingerprint := fingerprint text }) }

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

def checkSlice (fileMap : FileMap) (startPos stopPos : String.Pos.Raw)
    (acc : CommentAcc) : Except String CommentAcc :=
  if startPos < stopPos then
    scanTrivia fileMap ⟨fileMap.source, startPos, stopPos⟩ acc
  else
    .ok acc

def matchesLiteralToken (env : Environment) (token : Syntax) (raw : String) : Bool := Id.run do
  let parse (p : Parser.ParserFn) (input : String) : Option Syntax := do
    let s := p.run (Parser.InputContext.mk input "<token>") { env, options := {} } {}
      (Parser.mkParserState input)
    guard (!s.hasError && s.stackSize == 1)
    return s.stxStack.back
  match token with
  | .ident _ spelling .. =>
    let some (.ident _ parsed ..) := parse (Parser.tokenFn []) raw | return false
    return spelling.toString == raw && parsed.toString == raw
  | .node _ k _ =>
    unless token.isLit? k == some raw do return false
    if k == interpolatedStrLitKind then
      let chunk := if raw.startsWith "}" then "\"" ++ (raw.drop 1).toString else raw
      let emptyHole : Parser.ParserFn := fun _ s => s.pushSyntax .missing
      let some parsed := parse (Parser.interpolatedStrFn emptyHole) (chunk ++ "}\"") | return false
      return parsed[0].isLit? k == some chunk
    return ((parse (Parser.tokenFn []) raw).bind (·.isLit? k)) == some raw
  | _ => return false

def containsOpener (raw : String) : Bool :=
  raw.contains "--" || raw.contains "/-"

def crossesBoundary (raw : String) (next : Char) : Bool :=
  next == '-' && (raw.endsWith "-" || raw.endsWith "/")

def matchesBoundarySymbol (ctx : Parser.ParserContextCore) (token : Syntax) : Bool := Id.run do
  let leaf := match token with
    | .node _ _ #[arg] => arg
    | _ => token
  let .atom (.original _ start _ stop) spelling := leaf | return false
  let parsed := (Parser.symbolFn spelling).run ctx.toInputContext ctx.toParserModuleContext ctx.tokens
    { pos := start, cache := Parser.initCacheForInput ctx.inputString }
  return !parsed.hasError && parsed.stackSize == 1 && parsed.stxStack.back.getTailPos? == some stop

def checkToken (ctx : Parser.ParserContextCore) (token : Syntax) (raw : String) (next : Char)
    (start : String.Pos.Raw) : Except String Unit :=
  if (containsOpener raw || (crossesBoundary raw next && !matchesBoundarySymbol ctx token)) &&
      !matchesLiteralToken ctx.env token raw then
    .error s!"cannot account for a possible comment in the parser token at byte {start.byteIdx}"
  else .ok ()

theorem checkToken_ok_iff (ctx : Parser.ParserContextCore) (token : Syntax) (raw : String) (next : Char)
    (start : String.Pos.Raw) :
    checkToken ctx token raw next start = .ok () ↔
      matchesLiteralToken ctx.env token raw = true ∨
      (containsOpener raw = false ∧ (crossesBoundary raw next = false ∨ matchesBoundarySymbol ctx token = true)) := by
  simp only [checkToken]
  split <;> simp_all <;> grind

partial def collectSyntax (ctx : Parser.ParserContextCore) (prevPos nextPos : String.Pos.Raw) (stx : Syntax)
    (acc : CommentAcc) : Except String CommentAcc := do
  unless prevPos ≤ nextPos && nextPos ≤ ctx.endPos do
    throw "Lean's parser returned an invalid command range"
  let (pos, acc) ← walk stx prevPos acc
  checkSlice ctx.fileMap pos nextPos acc
where
  consume (pos start stop : String.Pos.Raw) (account : CommentAcc → Except String CommentAcc) (acc : CommentAcc) :
      Except String (String.Pos.Raw × CommentAcc) := do
    unless pos ≤ start && start ≤ stop && stop ≤ nextPos do
      throw s!"source range [{start.byteIdx}, {stop.byteIdx}) outside unread bytes [{pos.byteIdx}, {nextPos.byteIdx})"
    let acc ← checkSlice ctx.fileMap pos start acc
    return (stop, ← account acc)
  consumeToken (s : Syntax) (pos start stop : String.Pos.Raw) (acc : CommentAcc) :=
    consume pos start stop (fun a => do
      checkToken ctx s (ctx.extract start stop) (ctx.get stop) start
      return a) acc
  walk (s : Syntax) (pos : String.Pos.Raw) (acc : CommentAcc) :
      Except String (String.Pos.Raw × CommentAcc) := do
    match s with
    | .atom (.original _ start _ stop) _ | .ident (.original _ start _ stop) .. =>
      consumeToken s pos start stop acc
    | .node _ k args =>
      if k == ``Parser.Command.docComment || k == ``Parser.Command.plainDocComment ||
          k == ``Parser.Command.moduleDoc then
        let some (.original _ start ..) := s.getHeadInfo? | throw "docstring has no original start"
        let some (.original _ _ _ stop) := s.getTailInfo? | throw "docstring has no original end"
        let kind := if k == ``Parser.Command.moduleDoc then "moddoc" else "doc"
        consume pos start stop (recordSpan ctx.fileMap kind start stop) acc
      else if k == choiceKind then
        let some first := args[0]? | throw "empty parser choice"
        let (stop, acc) ← walk first pos acc
        let mut acc := acc
        for alt in args[1...*] do
          let (altStop, altAcc) ← walk alt pos acc
          unless altStop == stop do throw "parser alternatives cover different source ranges"
          acc := altAcc
        return (stop, acc)
      else if let #[.atom (.original _ start _ stop) _] := args then
        consumeToken s pos start stop acc
      else
        args.foldlM (fun (p, a) arg => walk arg p a) (pos, acc)
    | _ => return (pos, acc)

def sourceOrder (acc : CommentAcc) : Array Comment :=
  (acc.spans.toArray.qsort fun a b => a.1 < b.1).map (·.2.2)

def distinctCommentLines (comments : Array Comment) : Nat := Id.run do
  let mut ls : Std.HashSet Nat := {}
  for c in comments do
    for l in [c.startLine : c.endLine + 1] do
      ls := ls.insert l
  return ls.size

unsafe def commentsOfModule (file : String) (mod : Name) : IO (Array Comment) := do
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let fileMap := inputCtx.fileMap
  let endPos := fileMap.source.rawEndPos
  let opts := (({} : Options).setBool `Elab.async false).setBool `debug.byAsSorry true
  let fail (what : String) (messages : MessageLog) : IO (Array Comment) := do
    let shown ← messages.toList.mapM (·.toString)
    throw <| IO.userError s!"{file}: {what}, so its comments cannot be read:\n{String.join shown}"
  let scan (step : Except String CommentAcc) : IO CommentAcc :=
    match step with
    | .ok acc => pure acc
    | .error e => throw <| IO.userError s!"{file}: {e}"
  let headerEnv ← mkEmptyEnvironment
  let headerCtx : Parser.ParserContextCore := {
    toInputContext := inputCtx, env := headerEnv, options := {}, prec := 0
    tokens := Parser.Module.updateTokens (Parser.getTokenTable headerEnv) }
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  if messages.hasErrors then
    return ← fail "Lean's parser could not read its header" messages
  enableInitializersExecution
  let (env, messages) ← Elab.processHeader header opts messages inputCtx (mainModule := mod)
  if messages.hasErrors then
    return ← fail "Lean could not process its header" messages
  let mut cmdState := Elab.Command.mkState env messages opts
  let s ← Elab.IO.processCommandsIncrementally inputCtx parserState cmdState none
  if s.commandState.messages.hasErrors then
    return ← fail "Lean could not elaborate it" s.commandState.messages
  let mut acc ← scan <| collectSyntax headerCtx ⟨0⟩ parserState.pos header.raw {}
  let mut snap := s.initialSnap
  let mut prevPos := parserState.pos
  repeat
    let nextPos := snap.parserState.pos
    let scope := cmdState.scopes.head!
    let ctx : Parser.ParserContextCore := {
      toInputContext := inputCtx, env := cmdState.env, options := scope.opts
      currNamespace := scope.currNamespace, openDecls := scope.openDecls
      prec := 0, tokens := Parser.getTokenTable cmdState.env }
    acc ← scan <| collectSyntax ctx prevPos nextPos snap.stx acc
    prevPos := nextPos
    match snap.nextCmdSnap? with
    | some next =>
      cmdState := snap.elabSnap.resultSnap.get.cmdState
      snap := next.get
    | none => break
  unless prevPos == endPos do
    throw <| IO.userError s!"{file}: Lean's frontend stopped reading at byte {prevPos.byteIdx}, before the file's end at byte {endPos.byteIdx}, so what follows cannot be read for comments"
  return sourceOrder acc

unsafe def moduleComments (file : String) (dirs : SearchPath) : IO Unit := do
  let files ← trackedLeanFiles
  let mods ← moduleNames files
  let some mod := (files.zip mods).find? (·.1 == file) |>.map (·.2)
    | throw <| IO.userError s!"{file} is not a Lean file Git's index lists here"
  initSearchPath (← findSysroot) dirs
  for c in ← commentsOfModule file mod do
    IO.println s!"{c.fingerprint} {c.kind} {c.startLine} {c.endLine}"

def fileComments (toolDir libDir : System.FilePath) (file : String) : IO (Array Comment) := do
  let lines ← runSelf #["--comments-module", file, toolDir.toString, libDir.toString]
  lines.mapM fun line => do
    let unread : IO Comment :=
      throw <| IO.userError s!"{file}: --comments-module printed a line that is not a comment's: {line}"
    let [fp, kind, startLine, endLine] := line.splitOn " " | unread
    let (some startLine, some endLine) := (startLine.toNat?, endLine.toNat?) | unread
    unless isFingerprint fp && commentKinds.contains kind do
      return ← unread
    return { kind, startLine, endLine, fingerprint := fp }

def commentReaders : Nat := 3

partial def prepareToolImports (tools : Std.HashMap Name String) (out : System.FilePath)
    (searchPath : SearchPath) (imports : Array Name) (visiting : List Name := []) : IO Unit := do
  for mod in imports do
    let some file := tools.get? mod | continue
    if visiting.contains mod then
      throw <| IO.userError s!"{file}: cycle in tracked tool imports"
    let olean := modToFilePath out mod "olean"
    if ← olean.pathExists then continue
    prepareToolImports tools out searchPath (← importsOf file) (mod :: visiting)
    if let some dir := olean.parent then IO.FS.createDirAll dir
    let result ← IO.Process.output {
      cmd := "lean", args := #["-o", olean.toString, file],
      env := #[("LEAN_PATH", some searchPath.toString)] }
    unless result.exitCode == 0 do
      throw <| IO.userError s!"{file}: could not build imported tool:\n{result.stdout}{result.stderr}"

def projectComments (libDir : System.FilePath) (allFiles : Array String)
    (target? : Option String := none) :
    IO (Array (Array Comment)) := do
  let files ← match target? with
    | none => pure allFiles
    | some file => do
      unless allFiles.contains file do
        throw <| IO.userError s!"{file} is not a Lean file Git's index lists here"
      pure #[file]
  let toolFiles := allFiles.filter isToolFile
  let tools := Std.HashMap.ofList (((← moduleNames toolFiles).zip toolFiles).toList)
  IO.FS.withTempDir fun out => do
    let libPath := libDir :: (← addSearchPathFromEnv [])
    for file in files do
      prepareToolImports tools out (out :: libPath) (← importsOf file)
    let readers ← (Array.range commentReaders).mapM fun k => IO.asTask (prio := .dedicated) <|
      ((Array.range files.size).filter (· % commentReaders == k)).mapM fun i =>
        fileComments out libDir files[i]!
    let results ← readers.mapM fun reader => do pure (← IO.wait reader)
    let parts ← results.mapM IO.ofExcept
    return (Array.range files.size).map fun i => parts[i % commentReaders]![i / commentReaders]!

structure RatchetEntry where
  lines : Nat
  fingerprints : Array String

def parsePosNat (j : Json) (ctx : String) : IO Nat := do
  match j with
  | .num n =>
    if n.exponent == 0 && n.mantissa > 0 then
      return n.mantissa.toNat
    throw <| IO.userError s!"{ctx}: expected a positive integer, got {j}"
  | _ => throw <| IO.userError s!"{ctx}: expected a positive integer, got {j}"

def parseRatchet (source raw : String) : IO (Std.HashMap String RatchetEntry) := do
  let json ← match Json.parse raw with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"{source}: invalid JSON: {e}"
  let .arr entries := json
    | throw <| IO.userError s!"{source}: top-level JSON value must be an array"
  let mut map : Std.HashMap String RatchetEntry := {}
  for idx in [0 : entries.size] do
    let entry := s!"{source}[{idx}]"
    let .obj kvs := entries[idx]!
      | throw <| IO.userError s!"{entry}: entry must be a JSON object"
    let keys := kvs.toList.map (·.1)
    unless keys.length == 4 && ["file", "comments", "lines", "fingerprints"].all keys.contains do
      throw <| IO.userError s!"{entry}: entry must have exactly the keys file, comments, lines, fingerprints"
    let some (.str file) := kvs.get? "file"
      | throw <| IO.userError s!"{entry}: file must be a string"
    if file.isEmpty then
      throw <| IO.userError s!"{entry}: file must not be empty"
    if map.contains file then
      throw <| IO.userError s!"{entry}: duplicate entry for {file}"
    let some cJson := kvs.get? "comments"
      | throw <| IO.userError s!"{entry}: missing comments"
    let some lJson := kvs.get? "lines"
      | throw <| IO.userError s!"{entry}: missing lines"
    let some (.arr fpJson) := kvs.get? "fingerprints"
      | throw <| IO.userError s!"{entry}: fingerprints must be an array"
    let comments ← parsePosNat cJson s!"{entry}.comments ({file})"
    let lines ← parsePosNat lJson s!"{entry}.lines ({file})"
    let fingerprints ← fpJson.mapM fun j =>
      match j with
      | .str fp =>
        if isFingerprint fp then pure fp
        else throw <| IO.userError s!"{entry}.fingerprints ({file}): {fp} is not 16 lowercase hexadecimal digits"
      | _ => throw <| IO.userError s!"{entry}.fingerprints ({file}): expected a string, got {j}"
    unless fingerprints.size == comments do
      throw <| IO.userError s!"{entry} ({file}): comments is {comments}, but fingerprints holds {fingerprints.size}"
    for i in [1 : fingerprints.size] do
      if fingerprints[i]! < fingerprints[i - 1]! then
        throw <| IO.userError s!"{entry}.fingerprints ({file}): not in ascending order at {fingerprints[i]!}"
    map := map.insert file { lines, fingerprints }
  return map

def missingFrom (xs ys : Array String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut j := 0
  for x in xs do
    while j < ys.size && ys[j]! < x do
      j := j + 1
    if j < ys.size && ys[j]! == x then
      j := j + 1
    else
      out := out.push x
  return out

def baseRatchet : IO (Option (String × Std.HashMap String RatchetEntry)) := do
  for ref in ["origin/main", "main"] do
    let known ← IO.Process.output
      { cmd := "git", args := #["rev-parse", "--verify", "--quiet", ref ++ "^{commit}"] }
    unless known.exitCode == 0 do
      continue
    let merge ← IO.Process.output { cmd := "git", args := #["merge-base", "HEAD", ref] }
    if merge.exitCode == 1 then
      continue
    unless merge.exitCode == 0 do
      throw <| IO.userError s!"git merge-base HEAD {ref} failed:\n{merge.stderr}"
    let base := merge.stdout.trimAscii.toString
    let listed ← git #["ls-tree", "--full-tree", "--name-only", base, "--", ratchetFile]
    if listed.trimAscii.toString.isEmpty then
      return none
    let source := s!"{base}:{ratchetFile}"
    return some (base, ← parseRatchet source (← git #["show", source]))
  return none

def checkComments (libDir : System.FilePath) (allFiles : Array String) :
    IO (Array Rejection) := do
  let reject (message : String) : Rejection := { rule := "NO-COMMENTS", message }
  if allFiles.isEmpty then
    return #[reject "Git's index lists no Lean file"]
  let ratchet ← parseRatchet ratchetFile (← IO.FS.readFile ratchetFile)
  let mut errs : Array Rejection := #[]
  for (f, _) in ratchet.toList do
    unless allFiles.contains f do
      errs := errs.push (reject s!"{ratchetFile} lists {f}, which is not a Lean file Git's index lists")
  if let some (base, accepted) ← baseRatchet then
    for (f, entry) in ratchet.toList do
      let added := missingFrom entry.fingerprints ((accepted.get? f).elim #[] (·.fingerprints))
      unless added.isEmpty do
        errs := errs.push (reject s!"{ratchetFile} records for {f} {added.size} comment(s) that its copy at the merge base {base} does not record for that file, with the fingerprint(s) {" ".intercalate added.toList}; a file gains no comment")
  else
    IO.eprintln s!"NO-COMMENTS: no merge base of HEAD with origin/main or main holds {ratchetFile}, so its entries were compared with no earlier copy"
  for (f, comments) in allFiles.zip (← projectComments libDir allFiles) do
    let actual := (comments.map (·.fingerprint)).qsort (· < ·)
    let lines := distinctCommentLines comments
    let entry := ratchet.getD f { lines := 0, fingerprints := #[] }
    let added := missingFrom actual entry.fingerprints
    let gone := missingFrom entry.fingerprints actual
    unless added.isEmpty do
      let shown := (comments.filter (added.contains ·.fingerprint)).map fun c =>
        s!"{c.kind} L{c.startLine}-L{c.endLine} {c.fingerprint}"
      errs := errs.push (reject s!"{f} has {added.size} comment(s) that {ratchetFile} does not record for it, among: {", ".intercalate shown.toList}; a comment may be neither added nor edited, so delete them")
    unless gone.isEmpty do
      let fix := if actual.isEmpty then "remove its entry"
        else s!"set its comments to {actual.size} and its lines to {lines}, and remove the fingerprint(s) {" ".intercalate gone.toList}"
      errs := errs.push (reject s!"{f} no longer has {gone.size} comment(s) that {ratchetFile} records for it; {fix}")
    if added.isEmpty && gone.isEmpty && lines != entry.lines then
      errs := errs.push (reject s!"{f} has its comments across {lines} line(s), not the {entry.lines} that {ratchetFile} records; set its lines to {lines}")
  return errs

def listComments (target? : Option String) : IO Unit := do
  let allFiles ← trackedLeanFiles
  if allFiles.isEmpty then
    throw <| IO.userError "the project tracks no Lean file"
  let libDir := (← loadConfig).leanLibDir
  match target? with
  | some file =>
    let comments := (← projectComments libDir allFiles (some file))[0]!
    IO.println s!"{file}: {comments.size} comment(s), {distinctCommentLines comments} line(s)"
    for c in comments do
      IO.println s!"  {c.kind} L{c.startLine}-L{c.endLine} {c.fingerprint}"
  | none =>
    let mut files := 0
    let mut totComments := 0
    let mut totLines := 0
    for (f, comments) in allFiles.zip (← projectComments libDir allFiles) do
      unless comments.isEmpty do
        let lines := distinctCommentLines comments
        IO.println s!"{f}: {comments.size} comment(s), {lines} line(s)"
        files := files + 1
        totComments := totComments + comments.size
        totLines := totLines + lines
    IO.println s!"total: {files}/{allFiles.size} files with comments, {totComments} comment(s), {totLines} line(s)"

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
  let commentErrs ← checkComments pkg.leanLibDir allFiles
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
  | "--comments-module" :: file :: dir :: dirs =>
    Check.moduleComments file ((dir :: dirs).map System.FilePath.mk)
    return 0
  | ["--comments"] =>
    Check.listComments none
    return 0
  | ["--comments", file] =>
    Check.listComments (some file)
    return 0
  | [] =>
    let errs ← Check.check
    for e in errs do
      IO.println s!"[{e.rule}] {e.message}"
    return if errs.isEmpty then 0 else 1
  | _ => throw <| IO.userError "usage: lean --run tools/check.lean [--tests | --tests-module <file> <out> | --comments [<file>] | --comments-module <file> <searchDir>...]"
