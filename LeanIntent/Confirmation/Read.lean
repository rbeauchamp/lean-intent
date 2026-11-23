module

public import Lean
public import LeanIntent.Confirmation
public import LeanIntent.Render
public import LeanIntent.Loaded

public section

namespace LeanIntent.Confirmation.Read

open Lean Meta LeanIntent.Render

/-- Whether a discovered constant's safety permits relying on the proofs it holds. Definitions
must be `safe`: `ConstantInfo.isUnsafe` alone also admits `partial` definitions. Other kinds retain
Lean's unsafe flag check; opaque constants and axioms still fail when their values are read. -/
@[expose] def proofSafe : ConstantInfo → Bool
  | .defnInfo v =>
    match v.safety with
    | .safe => true
    | .unsafe | .partial => false
  | ci => !ci.isUnsafe

/-- The admission predicate requires exactly `safe` for every definition, covering every
`DefinitionSafety` constructor, and preserves the unsafe flag check for all other constants. -/
theorem proofSafe_iff (ci : ConstantInfo) : proofSafe ci = true ↔
    match ci with
    | .defnInfo v => v.safety = .safe
    | ci => ci.isUnsafe = false := by
  cases ci with
  | defnInfo v => cases h : v.safety <;> simp [proofSafe, h]
  | _ => simp [proofSafe]

/-- The name of the imported module at index `i`, read directly from `header.modules` (in Lean
v4.36.0's `src/Lean/Environment.lean`, line 165, `header.moduleNames` is a field initialized to
`modules.map (·.module)`). -/
@[expose] def moduleName? (header : EnvironmentHeader) (i : Nat) : Option Name :=
  header.modules[i]?.map (·.module)

/-- The definitions, opaque constants and axioms of the modules `mods`, the current one included when
it is listed, whose type, reduced by unfolding every definition, meets `test`, sorted by name; an
error when a module given is not imported, since it would hide what it declares, or when the
environment holds no data for one that is. An opaque constant or an axiom is found so that reading it
is an error, never a value passed over. A constant found that is unsafe or partial is an error too
(`proofSafe_iff`): such a definition may refer to itself, so
the proofs it holds, a deliverable's `keeps` or an implementation's `fulfils`, can prove anything,
and a safe declaration cannot refer to one, as Lean's kernel refuses
(`type_checker::infer_constant`).

A constant is of the module Lean records for its name (`Environment.const2ModIdx`), and of the
current one when Lean records none. Lean v4.36.0 records a module for a name only from that
module's `constNames` and from the `extraConstNames` of the data it reads as the module's IR
(`finalizeImport`, `src/Lean/Environment.lean`, lines 2697 to 2712), which is the module's own data
or its `.ir`, whose `extraConstNames` are the names of the IR declarations it stores
(`ImportedModule.irData?`, lines 2410 to 2418; `mkIRData`, lines 2233 to 2241 and `src/LeanIR.lean`,
lines 41 to 57). So the names read for a module given are its data's `constNames` and
`extraConstNames` and its stored IR declarations' names, each kept only where Lean records that
module for it, and each constant is found once. An environment that reads a module's `.ir.sig` as
its IR, which only Lean's `leanir` makes, is outside this account. -/
def declaredWhere (mods : Array Name) (test : Expr → MetaM Bool) : MetaM (Array Name) := asking do
  let env ← getEnv
  let modData := env.header.moduleData
  let mut selected : Array (ModuleIdx × ModuleData) := #[]
  let mut includeMain := false
  for m in mods do
    let idx? := env.getModuleIdx? m
    let isMain := m == env.mainModule
    unless isMain || idx?.isSome do
      throwError "the module {m} is not imported here, so what it declares cannot be read"
    if isMain then includeMain := true
    if let some idx := idx? then
      let i := idx.toNat
      if h : i < modData.size then
        selected := selected.push (idx, modData[i])
      else
        throwError "the environment holds no module data for {m} (index {i})"
  let isReadable (ci : ConstantInfo) : Bool :=
    ci matches .defnInfo _ | .opaqueInfo _ | .axiomInfo _
  let consts := env.constants
  let c2m := env.const2ModIdx
  let mut taken : Std.HashSet Name := {}
  let mut candidates : Array (Name × ConstantInfo) := #[]
  for (idx, data) in selected do
    let irNames := (IR.declMapExt.getModuleIREntries env idx).map (·.name)
    for names in #[data.constNames, data.extraConstNames, irNames] do
      for c in names do
        if c2m[c]? == some idx && !taken.contains c then
          if let some ci := consts.find? c then
            if isReadable ci then
              taken := taken.insert c
              candidates := candidates.push (c, ci)
  if includeMain then
    candidates := consts.map₂.foldl (init := candidates) fun acc c ci =>
      if isReadable ci && !c2m.contains c then acc.push (c, ci) else acc
    if consts.stage₁ then
      candidates := consts.map₁.fold (init := candidates) fun acc c ci =>
        if isReadable ci && !c2m.contains c then acc.push (c, ci) else acc
  let mut found := #[]
  for (c, ci) in candidates do
    if ← test (← readWhnf ci.type) then
      unless proofSafe ci do
        throwError "{c} is unsafe or partial, so its proofs could prove anything, and it is not read"
      found := found.push c
  return found.qsort Name.lt

/-- The constants of the modules `mods` whose type reduces to an application of `head`. -/
def declaredIn (mods : Array Name) (head : Name) : MetaM (Array Name) := asking <|
  declaredWhere mods fun t => pure (t.getAppFn.isConstOf head)

/-- The constant `decl`, with its own universe parameters. -/
def constOf (decl : Name) : MetaM Expr := asking do
  return mkConst decl ((← getConstInfo decl).levelParams.map .param)

/-- The name of the constant `e` is, or an error naming `what` must be one. -/
def constName (e : Expr) (what : String) : MetaM Name := asking do
  match e.consumeMData with
  | .const c _ => return c
  | e => throwError "{what} must be a constant, found{indentExpr e}"

theorem consequenceHeading_not_prefix_restatementPredicate :
    ¬ consequenceHeading.toList <+: restatementPredicate.toList := by
  decide

theorem consequenceBody_ne_restatementPredicate (predText defsText : String) :
    consequenceBody predText defsText ≠ restatementPredicate := by
  intro h
  have hp := consequenceBody_prefix predText defsText
  rw [h] at hp
  exact consequenceHeading_not_prefix_restatementPredicate hp

def questionOfVerified (c : Expr) :
    MetaM { q : Question // q.predicate ≠ restatementPredicate } := asking do
  let args ← ctorArgs c ``Consequence.mk 4
  let (kind, _) ← kindWords args[2]
  let ⟨pred, hp⟩ ← consequenceTextVerified args[3]
  return ⟨⟨← strLit args[1],
    if kind.isConstOf ``Consequence.Kind.entailment then .entailment else .possibility,
    pred⟩, by obtain ⟨p, d, rfl⟩ := hp; exact consequenceBody_ne_restatementPredicate p d⟩

/-- The question of the consequence `c`, a term of type `LeanIntent.Consequence W`. -/
def questionOf (c : Expr) : MetaM Question := asking <|
  return (← questionOfVerified c).1

/-- The kept answer of `a`, a term of type `LeanIntent.Attributed W`. -/
def keptOf (a : Expr) : MetaM (Question × Verdict × Answerer) := asking do
  let attributed ← ctorArgs a ``Attributed.mk 3
  let args ← ctorArgs attributed[1] ``Answer.mk 3
  return (← questionOf args[1], ← readVerdict args[2], ← readAnswerer attributed[2])

def deliverableParts (decl : Name) : MetaM (Name × Name × Vector Expr 5) := asking do
  let d ← ctorArgs (← constOf decl) ``Deliverable.mk 5
  return (← constName d[1] s!"the record of {decl}", ← constName d[2] s!"the explanation of {decl}",
    d)

def revisionOfVerified (decl : Name) :
    MetaM { rev : Revision // ∀ x ∈ rev.shown, x.1.predicate ≠ restatementPredicate } := asking do
  let (record, explanation, d) ← deliverableParts decl
  let ex ← ctorArgs (← constOf explanation) ``Explanation.mk 11
  let standing ← readRestatement ex[6]
  let shown ← (← listElems ex[7]).mapM fun e => do
    let s ← ctorArgs e ``Shown.mk 7
    let ⟨q, hq⟩ ← questionOfVerified s[3]
    return (⟨(q, ← readSettled standing s[6]), hq⟩ :
      { p : Question × Settled standing // p.1.predicate ≠ restatementPredicate })
  let kept ← (← listElems d[3]).mapM keptOf
  return ⟨⟨record.toString, ← revisionText explanation, standing,
      shown.toList.map (·.1), kept.toList⟩, fun _ hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact y.2⟩

/-- The current revision of the deliverable `decl`, a definition of type `LeanIntent.Deliverable W`,
as the build shows it. An error, naming what cannot be read or printed, when any of it cannot. -/
def revisionOf (decl : Name) : MetaM Revision := asking <|
  return (← revisionOfVerified decl).1

/-- The texts of the owners' log `decl`, a definition of type `LeanIntent.OwnersLog`. -/
def logTexts (decl : Name) : MetaM (List String) := asking do
  let args ← ctorArgs (← constOf decl) ``OwnersLog.mk 1
  return (← (← listElems args[0]).mapM strLit).toList

/-- The statements of the project's one owners' log among `mods`, or what is wrong. -/
def projectLog (mods : Array Name) : MetaM (Except (List Finding) (List String)) := asking do
  match (← declaredIn mods ``OwnersLog).toList with
  | [] => return .error [.noLog]
  | [log] => return .ok (← logTexts log)
  | logs => return .error [.severalLogs (logs.map toString)]

/-- Whether the explanation `ex` says someone settled something: it records an owner's confirmation
of the restatement, or an answer, or a derived consequence. -/
def explanationClaims (ex : Name) : MetaM Bool := asking do
  let ci ← getConstInfo ex
  let us := ci.levelParams.map .param
  withExplanationTelescope ci.type fun params _ => do
    let args ← ctorArgs (mkAppN (mkConst ex us) params) ``Explanation.mk 11
    let standing ← readRestatement args[6]
    let claims ← (← listElems args[7]).mapM fun e => do
      return (← readSettled standing (← ctorArgs e ``Shown.mk 7)[6]) matches .answered .. | .derived
    return standing != .unconfirmed || claims.any id

/-- The answers the constant `decl` holds, of type `LeanIntent.Attributed W` or a list of them. -/
def attributedOf (decl : Name) : MetaM (Array (Question × Verdict × Answerer)) := asking do
  let t ← readWhnf (← getConstInfo decl).type
  let e ← constOf decl
  (if t.getAppFn.isConstOf ``Attributed then pure #[e] else listElems e) >>= (·.mapM keptOf)

def undeclaredIn (mods decls : Array Name) (revs : Array Revision) : MetaM (List String) := asking do
  let held ← decls.mapM fun d => return (← deliverableParts d).2.1
  let kept := revs.toList.flatMap (·.kept)
  let explanations ← (← declaredWhere mods isExplanationType).filterM fun e =>
    return !held.contains e && (← explanationClaims e)
  let answers ← declaredWhere mods fun t => do
    if t.getAppFn.isConstOf ``Attributed then return true
    let .app (.const ``List _) arg := t | return false
    return (← readWhnf arg).getAppFn.isConstOf ``Attributed
  let strayAnswers ← answers.filterM fun a =>
    return (← attributedOf a).any fun x => !kept.contains x
  return (explanations ++ strayAnswers).toList.map toString

/-- **What a checker reads**, from the finished build: the report on the project whose modules are
`mods`. It is `Confirmation.report` of the texts of the project's one owners' log and the current
revision of each of its deliverables, with a finding for each value `undeclaredIn` names; so its
findings are empty exactly when there are none and the deliverables are confirmed
(`Report.withUndeclared_findings`, `Confirmation.report_findings`). A project with no log, or several,
has a report that says so. -/
def check (mods : Array Name) : MetaM Report := asking do
  match ← projectLog mods with
  | .error fs => return ⟨fs, [], [], [], []⟩
  | .ok texts =>
    let decls ← declaredIn mods ``Deliverable
    let revs ← decls.mapM revisionOf
    return (report texts revs.toList).withUndeclared (← undeclaredIn mods decls revs)

/-- The rendering of the deliverable `decl` of the project whose modules are `mods`, saying of who
settled each thing what the project's owners' log holds for this revision (`logStanding`,
`checked`), whatever the explanation still records: so a record revised after its owner confirmed it
does not print as confirmed. A log that cannot be read, or that `inForce` refuses, is an error. -/
def renderChecked (mods : Array Name) (decl : Name) : MetaM String := asking do
  let texts ← match ← projectLog mods with
    | .ok texts => pure texts
    | .error fs => throwError "the project's owners' log cannot be read: {fs.length} findings"
  let .ok log := parseLog texts | throwError "the project's owners' log cannot be read"
  let .ok (p, o) := inForce log | throwError "the project's owners' log is refused"
  let rev ← revisionOf decl
  let (_, explanation, _) ← deliverableParts decl
  let words := rev.shown.map fun x => String.ofList (checked p o log rev x.1 x.2).words
  renderExplanation explanation
    (statuses := .given (String.ofList (logStanding p o log rev).words) words.toArray)

def answerStatement (decl : Name) (question : Asked) (project id : Ident) (date : Date)
    (source : Source) (author : Authority) (verdict : Verdict) : MetaM String := asking do
  let rev ← revisionOf decl
  match buildAnswer rev question author verdict with
  | .ok answer => return Statement.print ⟨project, id, date, source, .answer answer⟩
  | .error msg => throwError "{decl} {msg}"

end LeanIntent.Confirmation.Read
