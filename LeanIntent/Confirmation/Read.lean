module

public import Lean
public import LeanIntent.Confirmation
public import LeanIntent.Render
public import LeanIntent.Loaded

public section

namespace LeanIntent.Confirmation.Read

open Lean Meta LeanIntent.Render

@[expose] def proofSafe : ConstantInfo → Bool
  | .defnInfo v =>
    match v.safety with
    | .safe => true
    | .unsafe | .partial => false
  | ci => !ci.isUnsafe

theorem proofSafe_iff (ci : ConstantInfo) : proofSafe ci = true ↔
    match ci with
    | .defnInfo v => v.safety = .safe
    | ci => ci.isUnsafe = false := by
  cases ci with
  | defnInfo v => cases h : v.safety <;> simp [proofSafe, h]
  | _ => simp [proofSafe]

@[expose] def moduleName? (header : EnvironmentHeader) (i : Nat) : Option Name :=
  header.modules[i]?.map (·.module)

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

def declaredIn (mods : Array Name) (head : Name) : MetaM (Array Name) := asking <|
  declaredWhere mods fun t => pure (t.getAppFn.isConstOf head)

def constOf (decl : Name) : MetaM Expr := asking do
  return mkConst decl ((← getConstInfo decl).levelParams.map .param)

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

def questionOf (c : Expr) : MetaM Question := asking <|
  return (← questionOfVerified c).1

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

def revisionOf (decl : Name) : MetaM Revision := asking <|
  return (← revisionOfVerified decl).1

def logTexts (decl : Name) : MetaM (List String) := asking do
  let args ← ctorArgs (← constOf decl) ``OwnersLog.mk 1
  return (← (← listElems args[0]).mapM strLit).toList

def projectLog (mods : Array Name) : MetaM (Except (List Finding) (List String)) := asking do
  match (← declaredIn mods ``OwnersLog).toList with
  | [] => return .error [.noLog]
  | [log] => return .ok (← logTexts log)
  | logs => return .error [.severalLogs (logs.map toString)]

def explanationClaims (ex : Name) : MetaM Bool := asking do
  let ci ← getConstInfo ex
  let us := ci.levelParams.map .param
  withExplanationTelescope ci.type fun params _ => do
    let args ← ctorArgs (mkAppN (mkConst ex us) params) ``Explanation.mk 11
    let standing ← readRestatement args[6]
    let claims ← (← listElems args[7]).mapM fun e => do
      return (← readSettled standing (← ctorArgs e ``Shown.mk 7)[6]) matches .answered .. | .derived
    return standing != .unconfirmed || claims.any id

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

def check (mods : Array Name) : MetaM Report := asking do
  match ← projectLog mods with
  | .error fs => return ⟨fs, [], [], [], []⟩
  | .ok texts =>
    let decls ← declaredIn mods ``Deliverable
    let revs ← decls.mapM revisionOf
    return (report texts revs.toList).withUndeclared (← undeclaredIn mods decls revs)

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
