import Lean
import LeanIntent.Confirmation
import LeanIntent.Render

/-!
# Reading a project's confirmations from the finished build

`LeanIntent.Confirmation` decides whether a project's deliverables are confirmed, given the texts of
its owners' log and the current revision of each. This module reads both from Lean's environment,
so a checker that reads only the declarations of a finished build (Regula's rule, for one) reads
them through the library, and parses no source text. Each input is read through Lean:

| Input | How it is read |
|---|---|
| the project's deliverables | every definition, opaque constant or axiom of the modules given whose type reduces, unfolding every definition, to `LeanIntent.Deliverable _` |
| the owners' log | the one such constant of those modules whose type so reduces to `LeanIntent.OwnersLog`; none, or several, is a finding |
| each statement's text | the list and its strings, reduced by Lean to `List.cons` and string literals, an error when one does not reduce to a literal, then `Statement.parse`, which accepts exactly the texts `Statement.print` writes |
| a deliverable's record and explanation | its constructor's arguments, each of which must be a constant, whose names the answers use |
| the revision's text | `LeanIntent.Render.revisionText` of the explanation, computed now, saying nothing of who settled what |
| each consequence's text | `LeanIntent.Render.consequenceText` of its predicate, computed now |
| the standing and statuses recorded | the explanation's and each answer's constructors, by `LeanIntent.Render`'s `readRestatement`, `readSettled` and `readAnswerer` |
| values no deliverable holds | every other constant of those modules whose type so reduces to `LeanIntent.Explanation _`, `LeanIntent.Attributed _` or a list of those answers (`undeclaredIn`), read the same way |

`check mods` gives the `Report`. The texts are computed from the build the check reads, so an answer
recorded against any other build's text, an older revision's or a definition's former body's, names
another text and does not count. A deliverable whose meaning reaches what cannot be printed fails
with an error naming it, never a pass, as does one that is not a constructor's application once
reduced, such as an opaque constant or an axiom.

The modules given are the caller's, and should be every module of the project, as Lake lists them:
a module left out hides what it declares, and an empty list finds no log. A constant whose type is
not one of these once unfolded, such as a function returning a deliverable or a structure holding
one, is not found, so it is not asked about; this is accepted, since it takes deliberately obscuring
a declaration that review reads.

`renderChecked` prints a deliverable's rendering with what the log holds of who settled each thing,
rather than what the explanation records. `answerStatement` writes the text of a new answer to one
question of a deliverable, with the two texts it must hold; a project commits that text as an entry
of its log.
-/

namespace LeanIntent.Confirmation.Read

open Lean Meta LeanIntent.Render

/-- The definitions, opaque constants and axioms of the modules `mods`, the current one included when
it is listed, whose type, reduced by unfolding every definition, meets `test`, sorted by name; an
error when a module given is not imported, since it would hide what it declares. An opaque constant
or an axiom is found so that reading it is an error, never a value passed over. -/
def declaredWhere (mods : Array Name) (test : Expr → MetaM Bool) : MetaM (Array Name) := do
  let env ← getEnv
  for m in mods do
    unless m == env.mainModule || env.header.moduleNames.contains m do
      throwError "the module {m} is not imported here, so what it declares cannot be read"
  let inMods := fun (c : Name) => match env.getModuleIdxFor? c with
    | some idx => env.header.moduleNames[idx.toNat]?.any mods.contains
    | none => mods.contains env.mainModule
  let candidates := env.constants.fold (init := #[]) fun acc c ci =>
    if (ci matches .defnInfo _ | .opaqueInfo _ | .axiomInfo _) && inMods c then acc.push (c, ci)
    else acc
  let mut found := #[]
  for (c, ci) in candidates do
    if ← withTransparency .all (do test (← whnf ci.type)) then found := found.push c
  return found.qsort Name.lt

/-- The constants of the modules `mods` whose type reduces to an application of `head`. -/
def declaredIn (mods : Array Name) (head : Name) : MetaM (Array Name) :=
  declaredWhere mods fun t => pure (t.getAppFn.isConstOf head)

/-- The constant `decl`, with its own universe parameters. -/
def constOf (decl : Name) : MetaM Expr := do
  return mkConst decl ((← getConstInfo decl).levelParams.map .param)

/-- The name of the constant `e` is, or an error naming `what` must be one. -/
def constName (e : Expr) (what : String) : MetaM Name := do
  match e.consumeMData with
  | .const c _ => return c
  | e => throwError "{what} must be a constant, found{indentExpr e}"

/-- The question of the consequence `c`, a term of type `LeanIntent.Consequence W`. -/
def questionOf (c : Expr) : MetaM Question := do
  let args ← ctorArgs c ``Consequence.mk 4
  let (kind, _) ← kindWords args[2]!
  return ⟨← strLit args[1]!,
    if kind.isConstOf ``Consequence.Kind.entailment then .entailment else .possibility,
    ← consequenceText args[3]!⟩

/-- The kept answer of `a`, a term of type `LeanIntent.Attributed W`. -/
def keptOf (a : Expr) : MetaM (Question × Verdict × Answerer) := do
  let attributed ← ctorArgs a ``Attributed.mk 3
  let args ← ctorArgs attributed[1]! ``Answer.mk 3
  return (← questionOf args[1]!, ← readVerdict args[2]!, ← readAnswerer attributed[2]!)

/-- The explanation of the deliverable `decl`, a definition of type `LeanIntent.Deliverable W`, by
its name, with the deliverable's constructor arguments. -/
def deliverableParts (decl : Name) : MetaM (Name × Name × Array Expr) := do
  let d ← ctorArgs (← constOf decl) ``Deliverable.mk 5
  return (← constName d[1]! s!"the record of {decl}", ← constName d[2]! s!"the explanation of {decl}",
    d)

/-- The current revision of the deliverable `decl`, a definition of type `LeanIntent.Deliverable W`,
as the build shows it. An error, naming what cannot be read or printed, when any of it cannot. -/
def revisionOf (decl : Name) : MetaM Revision := do
  let (record, explanation, d) ← deliverableParts decl
  let ex ← ctorArgs (← constOf explanation) ``Explanation.mk 11
  let standing ← readRestatement ex[6]!
  let shown ← (← listElems ex[7]!).mapM fun e => do
    let s ← ctorArgs e ``Shown.mk 7
    return (← questionOf s[3]!, ← readSettled standing s[6]!)
  let kept ← (← listElems d[3]!).mapM keptOf
  return ⟨record.toString, ← revisionText explanation, standing, shown.toList, kept.toList⟩

/-- The texts of the owners' log `decl`, a definition of type `LeanIntent.OwnersLog`. -/
def logTexts (decl : Name) : MetaM (List String) := do
  let args ← ctorArgs (← constOf decl) ``OwnersLog.mk 1
  return (← (← listElems args[0]!).mapM strLit).toList

/-- The statements of the project's one owners' log among `mods`, or what is wrong. -/
def projectLog (mods : Array Name) : MetaM (Except (List Finding) (List String)) := do
  match (← declaredIn mods ``OwnersLog).toList with
  | [] => return .error [.noLog]
  | [log] => return .ok (← logTexts log)
  | logs => return .error [.severalLogs (logs.map toString)]

/-- Whether the explanation `ex` says someone settled something: it records an owner's confirmation
of the restatement, or an answer, or a derived consequence. -/
def explanationClaims (ex : Name) : MetaM Bool := do
  let args ← ctorArgs (← constOf ex) ``Explanation.mk 11
  let standing ← readRestatement args[6]!
  let claims ← (← listElems args[7]!).mapM fun e => do
    return (← readSettled standing (← ctorArgs e ``Shown.mk 7)[6]!) matches .answered .. | .derived
  return standing != .unconfirmed || claims.any id

/-- The answers the constant `decl` holds, of type `LeanIntent.Attributed W` or a list of them. -/
def attributedOf (decl : Name) : MetaM (Array (Question × Verdict × Answerer)) := do
  let t ← withTransparency .all (whnf (← getConstInfo decl).type)
  let e ← constOf decl
  (if t.getAppFn.isConstOf ``Attributed then pure #[e] else listElems e) >>= (·.mapM keptOf)

/-- The values of the modules `mods`, among the deliverables `decls` with the current revisions
`revs`, that say who settled something and that no deliverable holds, which would print a claim the
check never asks about: an explanation that claims so and is no deliverable's, and an attributed
answer, or a list of them, holding one no deliverable keeps. These are all `LeanIntent.Render` prints
such words from, but for a term given to `answerText` directly. -/
def undeclaredIn (mods decls : Array Name) (revs : Array Revision) : MetaM (List String) := do
  let held ← decls.mapM fun d => return (← deliverableParts d).2.1
  let kept := revs.toList.flatMap (·.kept)
  let explanations ← (← declaredIn mods ``Explanation).filterM fun e =>
    return !held.contains e && (← explanationClaims e)
  let answers ← declaredWhere mods fun t => do
    if t.getAppFn.isConstOf ``Attributed then return true
    unless t.isAppOfArity ``List 1 do return false
    return (← whnf t.appArg!).getAppFn.isConstOf ``Attributed
  let strayAnswers ← answers.filterM fun a =>
    return (← attributedOf a).any fun x => !kept.contains x
  return (explanations ++ strayAnswers).toList.map toString

/-- **What a checker reads**, from the finished build: the report on the project whose modules are
`mods`. It is `Confirmation.report` of the texts of the project's one owners' log and the current
revision of each of its deliverables, with a finding for each value `undeclaredIn` names; so its
findings are empty exactly when there are none and the deliverables are confirmed
(`Report.withUndeclared_findings`, `Confirmation.report_findings`). A project with no log, or several,
has a report that says so. -/
def check (mods : Array Name) : MetaM Report := do
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
def renderChecked (mods : Array Name) (decl : Name) : MetaM String := do
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

/-- The text of a statement, made by `author` on `date` with the source `source`, answering the
question named `consequence` of the deliverable `decl`, at its current revision, with the two texts
that answer must hold. An error when the deliverable asks no such question. -/
def answerStatement (decl : Name) (consequence : String) (project id : Ident) (date : Date)
    (source : Source) (author : Authority) (verdict : Verdict) : MetaM String := do
  let rev ← revisionOf decl
  let some q := (restatement :: rev.shown.map (·.1)).find? (·.consequence == consequence)
    | throwError "{decl} asks no question named {consequence}"
  let answer : Statement.Answer :=
    { author, record := rev.record, revision := rev.text, consequence := q.consequence,
      kind := q.kind, predicate := q.predicate, verdict }
  return Statement.print ⟨project, id, date, source, .answer answer⟩

end LeanIntent.Confirmation.Read
