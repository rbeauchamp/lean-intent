import Lean
import LeanIntent.Explain
import LeanIntent.Print
import LeanIntent.Print.Meaning

/-!
# Rendering an intent record for its owner

`renderExplanation` renders an `Explanation r` as a Markdown document: the record `r`'s shape, each
domain hypothesis, property and vocabulary predicate, and each consequence shown to the owner, its
predicate printed exactly under a heading that says whether it is shown as an entailment or as a
possibility, each followed by its gloss in four parts; then every declaration the record's meaning
reaches outside Lean's own libraries, printed in full (`definitions`), and the Lean release whose
libraries those are (`toolchain`). `answerText` gives the canonical text of one of the owner's
answers to an explanation in the same way: the answer printed exactly; the explanation's name and
its record's statements and consequences, as the rendering prints them (`recordPart`); every
declaration the record's meaning and the answer reach, printed in full; and the toolchain.
`#render_intent e` shows the rendering of the explanation `e`, and `#answer_texts e l` the text of
each answer of the list `l` to the explanation `e`, as information. This module imports all of
Lean, so a project that only writes records and explanations need not import it.

The declarations a meaning reaches are those `LeanIntent.Print.meaning` collects from the constants
the printed terms name: the names each declaration's type mentions, a definition's value, an
inductive type's block, constructors and recursors, a constructor's inductive type, and a
recursor's block and rules, but not a theorem's proof or an opaque constant's value, which no term
that uses them depends on; for the rendering, also lean-intent's `IntentRecord.Meets`, which says
what it is for a subject to meet the record, and, when it shows consequences, `Consequence.HoldsOf`,
which says what it is for one to hold as shown; for an answer, those of the record it answers and
`Answer.KeptBy`, which says what it asks of every later revision. `LeanIntent.Print.meaning_ok`
proves that it collects every declaration reached, and nothing else. The meaning stops at the
declarations of Lean's own libraries, whose modules Lean found in the library directory of the
release that runs (`leanOwnModules`), and the text records that release and its commit instead;
the definitions of lean-intent itself are printed like a project's. For an intent record, and an
answer to it, it also stops at the record's own constant, whose meaning is shown statement by
statement.

Each declaration collected is printed in full, or the text is refused (`declSection`): a
definition's type and value; a theorem's, an opaque constant's and an axiom of a proposition's
type, which is all a term that uses one depends on; an inductive type's type, its number of
parameters and each constructor's type, which for a structure lists its fields; a function that
reads a field of a structure, whose value is checked to be the projection Lean makes, by its type,
the number of `fun`s of its value, its structure and its field's index, which determine its value
up to the names, types and annotations of those `fun`s (`projShape_determines`), while for a
well-typed definition its printed type fixes those types up to definitional equality, which is
argued, not proved. A constructor is printed with its inductive type and a
recursor is derived by Lean's kernel from its inductive types, so neither has a section of its own
once those are printed. An axiom whose type is not a proposition is refused, since in a module of
Lean's module system Lean shows an imported definition whose body is not exposed that way, as is a
name with no declaration and every type or value the printer cannot print or Lean does not read
back. So no text prints a meaning in part. The printer writes no `let` and no projection, and Lean
compiles a definition by structural or well-founded recursion into a value with projections, so a
meaning that reaches one is refused for now (lean-intent #22).

Every term is printed by `LeanIntent.Print.print`, whose output `LeanIntent.Print.parse` reads back
as the very term printed, for every term (`LeanIntent.Print.parse_print`), after
`LeanIntent.Print.eraseMData` removes its metadata, which Lean documents as definitionally equal to
the term it annotates, and `LeanIntent.Print.canon` renames the binders whose names cannot be
written or would be misread, which changes nothing but those names
(`LeanIntent.Print.eraseNames_canon`). Before a printed term is shown, Lean itself must read it
back: Lean's parser and elaborator, in the root namespace with nothing opened, must elaborate the
printed text to the same term, binder names, which Lean's kernel ignores, and metadata aside. When
they do not, the rendering is refused. So what the owner reads is what Lean
reads, for every term shown, though only as checked for that term and not as a theorem.

The rendering reads the explanation through Lean's own reduction to weak head normal form, so a
record, list or gloss built by any definition is read, as long as it reduces to its constructors;
a gloss must reduce to string literals. A statement is refused, and with it the rendering, when it
has free or meta variables, when the printer refuses it (`LeanIntent.Print.Printable` says which
terms it prints), when a part of its gloss is empty, or when Lean does not elaborate its printed
form back to it.

What is not proved: that the sections `declSection` writes print every part of a declaration, and
that the document as a whole, headings and prose included, determines what it prints, are argued
from this module's code, not stated as theorems; that a release's own libraries, named with its
version and commit, mean the same wherever that release runs is trusted with Lean.
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
opened and with the universe parameters of `e`, and elaborate it to `e`, binder names and metadata
aside. -/
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
        return !e'.hasMVar && (eraseNames (eraseMData e')).equal (eraseNames e)
      catch _ => return false

/-- `e` printed exactly, as text that Lean elaborates back to `e`, binder names and metadata aside;
an error when it cannot be. -/
def printExact (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then
    throwError "cannot print{indentExpr e}\nas it has free or meta variables"
  let ec := canon (constRoots e) [] (eraseMData e)
  let env ← getEnv
  let tokens := Parser.getTokenTable env
  let esc : String → Bool := fun s => (tokens.find? s).isSome
  for bare in [bareConsts env, fun _ => false] do
    match print bare esc ec with
    | none =>
      throwError "cannot print{indentExpr e}\nthe printer refuses it: it holds a `let`, \
        a projection, a universe metavariable, or a name it cannot write"
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

/-! ## The declarations a meaning reaches -/

/-- For each module the environment imports, whether it is one of Lean's own libraries: the first
component of its name is `Init`, `Std`, `Lean` or `Lake`, and Lean found its `.olean` file in the
library directory of the Lean release that runs (`Lean.findOLean`, `Lean.getLibDir`). A module of
a project that merely shares one of those names is not. -/
def leanOwnModules : MetaM (Array Bool) := do
  let env ← getEnv
  let lib := (← IO.FS.realPath (← getLibDir (← getBuildDir))).components
  env.header.moduleNames.mapM fun m => do
    unless [`Init, `Std, `Lean, `Lake].contains m.getRoot do return false
    return lib.isPrefixOf (← IO.FS.realPath (← findOLean m)).components

/-- Whether the meaning stops at the constant `c`: it is in `shown`, or declared in one of Lean's
own libraries (`own`, by module). -/
def stopAt (env : Environment) (own : Array Bool) (shown : NameSet) (c : Name) : Bool :=
  shown.contains c ||
    match env.getModuleIdxFor? c with
    | some idx => own[idx.toNat]?.getD false
    | none => false

/-- The universe parameters of a declaration, in words. -/
def univWords : List Name → String
  | [] => "no universe parameter"
  | [u] => s!"the universe parameter {u}"
  | us => s!"the universe parameters {", ".intercalate (us.map toString)}, in that order"

/-- The part `part` of the declaration `c`, `e`, printed exactly; an error naming both when it
cannot be. -/
def printPart (c : Name) (part : String) (e : Expr) : MetaM String := do
  try printExact e
  catch err => throwError "cannot print the {part} of {c}: {err.toMessageData}"

/-- The number `n` of the leading `fun`s of `e`, a structure `s` and a field index `i`, when `e` is
`fun x₁ ... xₙ => xₙ.i`, the projection of field `i` of `s` from the value of its last `fun`, with
`0 < n`. -/
def projShape : Expr → Option (Nat × Name × Nat)
  | .lam _ _ (.proj s i (.bvar 0)) _ => some (1, s, i)
  | .lam _ _ b _ => (projShape b).map fun (n, s, i) => (n + 1, s, i)
  | _ => none

/-- `n` `fun`s around `b`, each with no name, the type `Prop` and the default annotation. -/
def lamSkel : Nat → Expr → Expr
  | 0, b => b
  | n + 1, b => .lam .anonymous (.sort .zero) (lamSkel n b) .default

/-- `e` with the name, the type and the annotation of each of its leading `fun`s erased. -/
def eraseLams : Expr → Expr
  | .lam _ _ b _ => .lam .anonymous (.sort .zero) (eraseLams b) .default
  | e => e

/-- A term of the shape `projShape` describes is the projection it describes under its number of
`fun`s, once their names, types and annotations are erased. -/
theorem eraseLams_of_projShape {e : Expr} {n : Nat} {s : Name} {i : Nat}
    (h : projShape e = some (n, s, i)) : eraseLams e = lamSkel n (.proj s i (.bvar 0)) := by
  induction e generalizing n with
  | lam x t b bi _ ih =>
    unfold projShape at h
    split at h
    · rename_i heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Expr.lam.inj heq
      cases h
      rfl
    · rename_i heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Expr.lam.inj heq
      cases hb : projShape b with
      | none => simp [hb] at h
      | some d =>
        obtain ⟨m, s', i'⟩ := d
        simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp only [eraseLams, lamSkel, ih hb]
    · contradiction
  | _ => simp [projShape] at h

/-- Two terms with the same description by `projShape` are equal once the names, types and
annotations of their leading `fun`s are erased: the description determines everything else. -/
theorem projShape_determines {e₁ e₂ : Expr} {d : Nat × Name × Nat}
    (h₁ : projShape e₁ = some d) (h₂ : projShape e₂ = some d) : eraseLams e₁ = eraseLams e₂ := by
  obtain ⟨n, s, i⟩ := d
  rw [eraseLams_of_projShape h₁, eraseLams_of_projShape h₂]

/-- The description by `projShape` of the value of the definition `v`, without its metadata, when
that value is a projection of the kind Lean makes for a field, of a structure: an inductive type of
one block, with no index and one constructor, which has more fields than the index. The number of
the value's `fun`s, the structure and the field's index determine the value up to the names, types
and annotations of those `fun`s (`projShape_determines`). -/
def projectionOf (lookup : Name → Option ConstantInfo) (v : DefinitionVal) :
    Option (Nat × Name × Nat) :=
  match projShape (eraseMData v.value) with
  | some (n, s, i) =>
    match lookup s with
    | some (.inductInfo iv) =>
      match iv.ctors, iv.all with
      | [k], [_] =>
        match lookup k with
        | some (.ctorInfo kv) =>
          if iv.numIndices = 0 ∧ i < kv.numFields then some (n, s, i) else none
        | _ => none
      | _, _ => none
    | _ => none
  | none => none

/-- The section that prints the declaration `ci`, named `c`, in full, from the declarations `out`
that `LeanIntent.Print.meaning` collected; `none` for a constructor, printed with its inductive
type, and for a recursor, which Lean's kernel derives from its inductive types, when `out` holds
those; an error, naming what cannot be printed, otherwise. A function that reads a field of a
structure is printed by its type and its description by `projectionOf`, which determines its value
up to the names, types and annotations of its leading `fun`s (`projShape_determines`); for a
well-typed definition, its printed type fixes those types up to definitional equality, which is
argued, not proved. -/
def declSection (lookup : Name → Option ConstantInfo) (out : List (Name × ConstantInfo))
    (c : Name) (ci : ConstantInfo) : MetaM (Option String) := do
  let has (n : Name) : Bool := out.any (·.1 == n)
  match ci with
  | .ctorInfo v =>
    unless has v.induct do throwError "cannot print {c}: its inductive type is not printed"
    return none
  | .recInfo v =>
    unless v.all.all has do throwError "cannot print {c}: its inductive types are not printed"
    return none
  | _ => pure ()
  let type ← printPart c "type" ci.type
  let head (words : String) :=
    s!"### {c}\n\n{words}. It has {univWords ci.levelParams}. Its type:\n\n{code type}\n"
  match ci with
  | .ctorInfo _ | .recInfo _ => return none
  | .defnInfo v =>
    match projectionOf lookup v with
    | some (n, s, i) =>
      return some (head s!"A function that reads a field of a structure: its value is `fun` over \
        its first {n} arguments and returns field number {i + 1}, counted after the parameters in \
        the type of {s}'s constructor, of its argument number {n}, a value of {s}")
    | none =>
      let value ← printPart c "value" v.value
      return some (head "A definition" ++ s!"Its value:\n\n{code value}\n")
  | .thmInfo _ =>
    return some (head "A theorem, whose proof is not printed: any two proofs of a proposition are \
      equal by definitional proof irrelevance, so a term that uses it depends on nothing but its \
      statement")
  | .opaqueInfo _ =>
    return some (head "An opaque constant, whose value is not printed: Lean's kernel never unfolds \
      it, so a term that uses it depends on nothing but its type")
  | .axiomInfo v =>
    unless ← isProp v.type do
      throwError "cannot print {c}: it is an axiom whose type is not a proposition, whose meaning \
        is not all in its type; in a module of Lean's module system, Lean shows an imported \
        definition whose body is not exposed this way"
    return some (head "An axiom of a proposition: a term that uses it depends on nothing but its \
      statement, as for a theorem, which is how Lean's module system shows an imported theorem")
  | .quotInfo _ =>
    return some (head "A primitive of quotient types, which Lean's kernel defines")
  | .inductInfo v =>
    let words := if isStructure (← getEnv) c then "A structure: an inductive type with one \
        constructor, whose arguments after its parameters are the structure's fields, in order"
      else "An inductive type"
    let mut s := head words ++ s!"Of the arguments its type takes, the first {v.numParams} are \
      parameters and the other {v.numIndices} indices."
    if v.all.length > 1 then
      s := s ++ s!" It is declared in one block of mutually inductive types, \
        {", ".intercalate (v.all.map toString)}, each printed here."
    s := s ++ " Its recursor is the one Lean's kernel derives from this declaration."
    if v.ctors.isEmpty then return some (s ++ " It has no constructor.\n\n")
    s := s ++ " Its constructors, in order, each with its type:\n\n"
    for k in v.ctors do
      match lookup k with
      | some (.ctorInfo kv) => s := s ++ s!"#### {k}\n\n{code (← printPart k "type" kv.type)}\n"
      | _ => throwError "cannot print {c}: its constructor {k} has no declaration here"
    return some s

/-- The toolchain the rendering is made with, whose libraries are not printed. -/
def toolchain : String :=
  s!"## Lean's own libraries\n\nThe declarations of Lean's own libraries (Init, Std, Lean and \
    Lake) are not printed: they are those of Lean {Lean.versionString}, commit {Lean.githash}, \
    which made this text. A declaration is counted as Lean's own when Lean found the module that \
    declares it in that release's library directory.\n"

/-- Every declaration the constants `roots` reach (`LeanIntent.Print.meaning`), outside Lean's own
libraries and `shown`, printed in full by `declSection`, in the order they are reached; an error,
naming what cannot be printed, when one cannot be, so nothing is printed in part. -/
def definitions (roots : List Name) (shown : NameSet) : MetaM String := do
  let env ← getEnv
  let lookup := fun c => (env.setExporting false).find? c
  let out ← match meaning lookup (stopAt env (← leanOwnModules) shown) roots with
    | .ok out => pure out
    | .error (.unknown c) => throwError "cannot print {c}: it has no declaration here"
    | .error .fuel => throwError "cannot print the definitions: there are too many"
  let mut text := ""
  for (c, ci) in out do
    if let some s ← declSection lookup out c ci then text := text ++ s
  return text

/-- The kind of a consequence, `e` reduced to its constructor, and what it is shown as. -/
def kindWords (e : Expr) : MetaM (Expr × String) := do
  let kind ← whnf e
  if kind.isConstOf ``Consequence.Kind.entailment then
    return (kind, "an entailment: every subject that meets the record satisfies it")
  else if kind.isConstOf ``Consequence.Kind.possibility then
    return (kind, "a possibility: some subject that meets the record satisfies it")
  else throwError "expected the kind of a consequence, found{indentExpr kind}"

/-- The rendering of the explanation `decl`, a constant of type `LeanIntent.Explanation r`, up to
its definitions: the record's shape and statements and the consequences shown, each printed exactly
with its gloss; with the constants the record's meaning starts from, and the record's own constant,
at which it stops. -/
def recordPart (decl : Name) : MetaM (String × List Name × NameSet) := do
  let ci ← getConstInfo decl
  let ex ← ctorArgs (mkConst decl (ci.levelParams.map .param)) ``Explanation.mk 10
  let r ← ctorArgs ex[1]! ``IntentRecord.mk 5
  let mut doc := s!"# The intent record {← printExact ex[1]!}\n\n\
    Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its \
    kernel checks, binder names and metadata aside, from the root namespace with nothing opened. \
    The plain words after it are written by a model and are trusted, not proved.\n\n## Shape\n\n"
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
    let (_, shownAs) ← kindWords c[2]!
    doc := doc ++ statement s!"{← strLit c[1]!}, {shownAs}" (← printExact c[3]!) (← readGloss s[4]!)
    printed := printed.push c[3]!
  -- The record's own constant is the record shown above, statement by statement. What it means for
  -- a subject to meet the record, and for a consequence to hold of it as shown, are lean-intent's
  -- definitions, printed with the rest.
  let shown : NameSet := if let .const c _ := ex[1]! then ({} : NameSet).insert c else {}
  let roots := printed.toList.flatMap (exprRefs · []) ++ [``IntentRecord.Meets] ++
    if consequences.isEmpty then [] else [``Consequence.HoldsOf]
  return (doc, roots, shown)

/-- The rendering of the explanation `decl`, a constant of type `LeanIntent.Explanation r`: its
record part (`recordPart`), every declaration that part's meaning reaches, and the toolchain. -/
def renderExplanation (decl : Name) : MetaM String := do
  let (doc, roots, shown) ← recordPart decl
  return doc ++ s!"## Definitions the record's meaning reaches\n\nThese are not statements of the \
    record: each is a declaration that a statement above depends on, or that says what it is for \
    a subject to meet the record and for a consequence to hold of it as shown, with everything \
    those depend on in turn. Each is printed in full: its type, a definition's value, and an \
    inductive type's constructors, which for a structure are its fields; a theorem's proof and an \
    opaque constant's value are not, since no term that uses them depends on more than their \
    types. Their plain words are those of the statements that use them.\n\n\
    {← definitions roots shown}{toolchain}"

/-! ## The owner's answers -/

/-- The canonical text of the owner's answer `a`, a term of type `LeanIntent.Answer W`, to the
explanation `ex`, a constant of type `LeanIntent.Explanation r`: the answer printed exactly, with
its consequence's name, kind and predicate and its verdict, each reduced to its constructor or
literal; then the name of `ex` and its record part (`recordPart`), the record's statements and the
consequences shown, as its rendering prints them; then every declaration the record part and the
answer reach, `LeanIntent.Answer.KeptBy`'s among them, which says what the answer asks of every
later revision, each printed in full by one call of `definitions`; and the toolchain. An error,
naming what cannot be printed, when any of it cannot be. -/
def answerText (ex : Name) (a : Expr) : MetaM String := do
  let ans ← ctorArgs a ``Answer.mk 3
  let c ← ctorArgs ans[1]! ``Consequence.mk 4
  let aus := (← whnf a).getAppFn.constLevels!
  let cus := (← whnf ans[1]!).getAppFn.constLevels!
  let name ← whnf c[1]!
  unless name matches .lit (.strVal _) do
    throwError "expected a string literal, found{indentExpr name}"
  let (kind, shownAs) ← kindWords c[2]!
  let verdict ← whnf ans[2]!
  let verdictWords ←
    if verdict.isConstOf ``Verdict.confirmed then pure "confirmed"
    else if verdict.isConstOf ``Verdict.declined then pure "declined"
    else throwError "expected the owner's verdict, found{indentExpr verdict}"
  let term := mkApp3 (.const ``Answer.mk aus) ans[0]!
    (mkApp4 (.const ``Consequence.mk cus) c[0]! name kind c[3]!) verdict
  let answer := s!"# An answer of the owner\n\nThe owner {verdictWords} the consequence \
    {repr (← strLit name)}, shown as {shownAs}. The answer, printed exactly: as Lean syntax that \
    Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the \
    root namespace with nothing opened.\n\n{code (← printExact term)}\n"
  let exConst := mkConst ex ((← getConstInfo ex).levelParams.map .param)
  let explained := s!"# The explanation it answers\n\nThe answer is given to the explanation \
    below, printed exactly, whose record and consequences follow as its rendering prints \
    them.\n\n{code (← printExact exConst)}\n"
  let (record, roots, shown) ← recordPart ex
  return answer ++ explained ++ record ++ s!"## Definitions the answer and the record reach\n\n\
    These are not statements of the record or of the answer: each is a declaration that the \
    answer or a statement above depends on, or that says what it is for a subject to meet the \
    record, for a consequence to hold of it as shown, and what the answer asks of every later \
    revision of the record (`LeanIntent.Answer.KeptBy`), with everything those depend on in turn, \
    each printed in full as in the rendering of a record.\n\n\
    {← definitions (roots ++ exprRefs term [] ++ [``Answer.KeptBy]) shown}{toolchain}"

/-- The canonical text of each answer of the list `e` of the owner's answers to the explanation
`ex` (`answerText`). -/
def answerTexts (ex : Name) (e : Expr) : MetaM (Array String) := do
  (← listElems e).mapM (answerText ex)

/-- `#render_intent e` shows the rendering of the explanation `e`. -/
syntax (name := renderIntent) "#render_intent " ident : command

@[command_elab renderIntent]
def elabRenderIntent : Command.CommandElab := fun stx => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  logInfo (← Command.liftTermElabM <| renderExplanation decl)

/-- `#answer_texts ex e` shows the canonical text of each answer of the list `e` of the owner's
answers to the explanation `ex`. -/
syntax (name := answerTextsCmd) "#answer_texts " ident ident : command

@[command_elab answerTextsCmd]
def elabAnswerTexts : Command.CommandElab := fun stx => do
  let ex ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[2]
  let texts ← Command.liftTermElabM do
    let ci ← getConstInfo decl
    answerTexts ex (mkConst decl (ci.levelParams.map .param))
  for text in texts do logInfo text

end LeanIntent.Render
