import Lean
import LeanIntent.Explain
import LeanIntent.Print

/-!
# Rendering an intent record for its owner

`renderExplanation` renders an `Explanation r` as a Markdown document: the record `r`'s shape, each
domain hypothesis, property and vocabulary predicate, and each consequence shown to the owner, its
predicate printed exactly under a heading that says whether it is shown as an entailment or as a
possibility, each followed by its gloss in four parts; then the definitions the printed statements
use from outside Lean's own libraries and this one, each printed with its type and, for a
definition, its value.
`#render_intent e` shows the rendering of the explanation `e` as information. This module imports
all of Lean, so a project that only writes records and explanations need not import it.

Every term is printed by `LeanIntent.Print.print`, whose output `LeanIntent.Print.parse` reads back
as the very term printed, for every term (`LeanIntent.Print.parse_print`), after
`LeanIntent.Print.canon` renames the binders whose names cannot be written or would be misread,
which changes nothing but those names (`LeanIntent.Print.eraseNames_canon`). Before a printed term is
shown, Lean itself must read it back: Lean's parser and elaborator, in the root namespace with
nothing opened, must elaborate the printed text to the same term, binder names aside, which Lean's
kernel ignores. When they do not, the rendering is refused. So what the owner reads is what Lean
reads, for every term shown, though only as checked for that term and not as a theorem.

The rendering reads the explanation through Lean's own reduction to weak head normal form, so a
record, list or gloss built by any definition is read, as long as it reduces to its constructors;
a gloss must reduce to string literals. A statement is refused, and with it the rendering, when it
has free or meta variables, when the printer refuses it (`LeanIntent.Print.Printable` says which
terms it prints), when a part of its gloss is empty, or when Lean does not elaborate its printed
form back to it. The definitions the statements use are not statements of the record, but the
meaning of names the statements use; one whose type or value cannot be printed is listed with a
note saying so, in place of the part that cannot.
-/

namespace LeanIntent.Render

open Lean Meta Elab LeanIntent.Print

/-- Whether every binder of the leading `∀`s of `t` has the default annotation. -/
def explicitOnly : Expr → Bool
  | .forallE _ _ b bi => bi.isExplicit && explicitOnly b
  | _ => true

/-- The constants written without `@`: those whose type has only binders with the default
annotation, which Lean applies to the arguments written after them and nothing else. -/
def bareConsts (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some ci => explicitOnly ci.type
  | none => false

/-- Whether Lean's parser and elaborator read `text` as a term, in the root namespace with nothing
opened and with the universe parameters of `e`, and elaborate it to `e`, binder names aside. -/
def elaboratesTo (text : String) (e : Expr) : MetaM Bool := do
  match Parser.runParserCategory (← getEnv) `term text with
  | .error _ => return false
  | .ok stx =>
    let lvls := (collectLevelParams {} e).params.toList
    withoutModifyingState do
      try
        let e' ← withTheReader Core.Context
            (fun ctx => { ctx with currNamespace := .anonymous, openDecls := [] }) do
          Term.TermElabM.run' <| Term.withLevelNames lvls <| Term.withoutErrToSorry do
            let e' ← Term.elabTerm stx none
            Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e'
        return !e'.hasMVar && (eraseNames e').equal (eraseNames e)
      catch _ => return false

/-- `e` printed exactly, as text that Lean elaborates back to `e`; an error when it cannot be. -/
def printExact (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then
    throwError "cannot print{indentExpr e}\nas it has free or meta variables"
  let ec := canon (constRoots e) [] e
  let env ← getEnv
  let tokens := Parser.getTokenTable env
  let esc : String → Bool := fun s => (tokens.find? s).isSome
  for bare in [bareConsts env, fun _ => false] do
    match print bare esc ec with
    | none =>
      throwError "cannot print{indentExpr e}\nthe printer refuses it: it holds a `let`, \
        metadata, a projection, a universe metavariable, or a name it cannot write"
    | some text =>
      if ← elaboratesTo text ec then return text
  throwError "cannot print{indentExpr e}\nLean does not elaborate its printed form back to it"

/-! ## Reading an explanation -/

/-- The arguments of `e`, which must reduce to the constructor `ctor` applied to `n` arguments. -/
def ctorArgs (e : Expr) (ctor : Name) (n : Nat) : MetaM (Array Expr) := do
  let e ← whnf e
  unless e.isAppOfArity ctor n do
    throwError "expected {.ofConstName ctor} applied to {n} arguments, found{indentExpr e}"
  return e.getAppArgs

/-- The elements of a list. -/
partial def listElems (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``List.cons 3 then
    return #[e.getArg! 1] ++ (← listElems (e.getArg! 2))
  else if e.isAppOfArity ``List.nil 1 then
    return #[]
  else throwError "expected a list, found{indentExpr e}"

/-- The string a string literal is. -/
def strLit (e : Expr) : MetaM String := do
  match ← whnf e with
  | .lit (.strVal s) => return s
  | e => throwError "expected a string literal, found{indentExpr e}"

/-- A gloss's four parts, in order: what it requires, rules out, still allows, and the freedom it
leaves. -/
def readGloss (e : Expr) : MetaM (Array String) := do
  let parts ← (← ctorArgs e ``Gloss.mk 4).mapM strLit
  for (label, s) in #["requires", "rules out", "still allows", "freedom"].zip parts do
    if s.trimAscii.isEmpty then throwError "the gloss's part on what it {label} is empty"
  return parts

/-! ## The document -/

/-- A Markdown code fence longer than every run of backticks in `text`. -/
def fence (text : String) : String :=
  let longest := (text.toList.foldl (fun (run, best) c =>
    if c = '`' then (run + 1, max best (run + 1)) else (0, best)) (0, 0)).2
  String.ofList (List.replicate (max 3 (longest + 1)) '`')

/-- A block of Lean code. -/
def code (text : String) : String :=
  let f := fence text
  s!"{f}lean\n{text}\n{f}\n"

/-- A statement: its heading, its exact print and its gloss. -/
def statement (heading text : String) (gloss : Array String) : String :=
  s!"### {heading}\n\n{code text}\n- **Requires:** {gloss[0]!}\n- **Rules out:** {gloss[1]!}\n\
    - **Still allows:** {gloss[2]!}\n- **Freedom O5 leaves:** {gloss[3]!}\n\n"

/-- Whether `c` is declared outside Lean's own libraries and this one. -/
def outside (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => true
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some m => !([`Init, `Std, `Lean, `Lake, `LeanIntent].contains m.getRoot)
    | none => true

/-- Whether only a declaration's type is shown: Lean made it, or it is not a definition. -/
def typeOnly (env : Environment) (ci : ConstantInfo) : Bool :=
  !ci.isDefinition || isAuxRecursor env ci.name || isNoConfusion env ci.name ||
    isMatcherCore env ci.name || ci.name.isInternal

/-- The definitions the terms `es` use from outside Lean's own libraries and this one, and those
they use in turn, each with its type and, for a definition, its value; `shown` are left out, as
already shown. -/
def dependencies (es : Array Expr) (shown : NameSet) : MetaM String := do
  let env ← getEnv
  let mut queue := es.foldl (fun acc e => acc ++ e.getUsedConstants) #[]
  let mut seen : NameSet := shown
  let mut out := ""
  let mut i := 0
  while h : i < queue.size do
    let c := queue[i]
    i := i + 1
    if seen.contains c || !outside env c then continue
    seen := seen.insert c
    let ci ← getConstInfo c
    out := out ++ s!"### {c}\n\n"
    try
      out := out ++ s!"Its type:\n\n{code (← printExact ci.type)}\n"
      queue := queue ++ ci.type.getUsedConstants
    catch err =>
      out := out ++ s!"Its type is not shown: {← err.toMessageData.toString}\n\n"
    if !typeOnly env ci then
      if let some v := ci.value? then
        try
          out := out ++ s!"Its value:\n\n{code (← printExact v)}\n"
          queue := queue ++ v.getUsedConstants
        catch err =>
          out := out ++ s!"Its value is not shown: {← err.toMessageData.toString}\n\n"
  return out

/-- The rendering of the explanation `decl`, a constant of type `LeanIntent.Explanation r`. -/
def renderExplanation (decl : Name) : MetaM String := do
  let ci ← getConstInfo decl
  let ex ← ctorArgs (mkConst decl (ci.levelParams.map .param)) ``Explanation.mk 10
  let r ← ctorArgs ex[1]! ``IntentRecord.mk 5
  let mut doc := s!"# The intent record {← printExact ex[1]!}\n\n\
    Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its \
    kernel checks, from the root namespace with nothing opened. The plain words after it are written \
    by a model and are trusted, not proved.\n\n## Shape\n\n"
  let mut printed : Array Expr := #[ex[1]!]
  doc := doc ++ statement "The subject" (← printExact r[1]!) (← readGloss ex[2]!)
  printed := printed.push r[1]!
  for (title, items, glosses, ctor) in
      [("Domain hypotheses", r[2]!, ex[3]!, ``Clause.mk), ("Properties", r[3]!, ex[4]!, ``Clause.mk),
        ("Vocabulary", r[4]!, ex[5]!, ``Pred.mk)] do
    let items ← listElems items
    let glosses ← listElems glosses
    unless items.size == glosses.size do
      throwError "{title}: the record has {items.size} and the explanation {glosses.size} glosses"
    doc := doc ++ s!"## {title}\n\n"
    if items.isEmpty then doc := doc ++ "None.\n\n"
    for (item, gloss) in items.zip glosses do
      let a ← ctorArgs item ctor 3
      if ctor == ``Pred.mk then
        let heading := s!"{← strLit a[0]!}, a predicate over `{← printExact a[1]!}`"
        doc := doc ++ statement heading (← printExact a[2]!) (← readGloss gloss)
        printed := printed ++ #[a[1]!, a[2]!]
      else
        doc := doc ++ statement (← strLit a[1]!) (← printExact a[2]!) (← readGloss gloss)
        printed := printed.push a[2]!
  doc := doc ++ "## Consequences, each to confirm or decline\n\n"
  let consequences ← listElems ex[6]!
  if consequences.isEmpty then doc := doc ++ "None.\n\n"
  for shown in consequences do
    let s ← ctorArgs shown ``Shown.mk 5
    let c ← ctorArgs s[2]! ``Consequence.mk 4
    let kind ← whnf c[2]!
    let shownAs ←
      if kind.isConstOf ``Consequence.Kind.entailment then
        pure "an entailment: every subject that meets the record satisfies it"
      else if kind.isConstOf ``Consequence.Kind.possibility then
        pure "a possibility: some subject that meets the record satisfies it"
      else throwError "expected the kind of a consequence, found{indentExpr kind}"
    doc := doc ++ statement s!"{← strLit c[1]!}, {shownAs}" (← printExact c[3]!) (← readGloss s[4]!)
    printed := printed.push c[3]!
  -- The record's own constant is the record shown above, statement by statement.
  let shown : NameSet := if let .const c _ := ex[1]! then ({} : NameSet).insert c else {}
  let deps ← dependencies printed shown
  unless deps.isEmpty do
    doc := doc ++ s!"## Definitions the statements use\n\nThese are not statements of the record: \
      each is the definition of a name a statement above uses, printed exactly so that the statement \
      can be read to the end. Its plain words are those of the statements that use it.\n\n{deps}"
  return doc

/-- `#render_intent e` shows the rendering of the explanation `e`. -/
syntax (name := renderIntent) "#render_intent " ident : command

@[command_elab renderIntent]
def elabRenderIntent : Command.CommandElab := fun stx => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  logInfo (← Command.liftTermElabM <| renderExplanation decl)

end LeanIntent.Render
