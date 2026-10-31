import Lean
import LeanIntent.Explain
import LeanIntent.Print
import LeanIntent.Print.Meaning
import LeanIntent.Cone
import LeanIntent.Generic

/-!
# Rendering an intent record for its owner

`renderExplanation` renders an `Explanation r` as a Markdown document: whether an owner confirmed
the record's restatement; the record `r`'s shape, each
domain hypothesis, property and vocabulary predicate, and each consequence shown with it, its
predicate printed under a heading that says whether it is shown as an entailment or as a
possibility, each followed by who settled it and its gloss in four parts; then every declaration the
record's meaning reaches outside Lean's own libraries, printed in full (`definitions`), and the Lean
release whose libraries those are (`toolchain`). A rendering prints in one of two forms (`Form`):
readable, the default, with Lean's notation and without what Lean infers, or exact, with every
implicit argument, by the audited printer. `answerText` gives the canonical text of one
attributed answer to an explanation in the same way: who gave it and the answer printed exactly; the
explanation's name and its record's statements and consequences, as the exact form prints them
(`recordPart`); every declaration the record's meaning and the answer reach, printed in full; and the
toolchain. `#render_intent e` shows the rendering of the explanation `e`, `#render_intent_exact e`
the same in the exact form, `#render_intent_at e a₁ … aₙ` the rendering of a generic explanation at
the representative values `a₁ … aₙ`, and `#answer_texts e l` the text of each attributed answer of
the list `l` to the explanation `e`, as information. An answer recorded in a project's owners' log
holds two other texts (`LeanIntent.Confirmation`), both printed exactly: the rendering saying nothing
of who settled what (`revisionText`), as the revision it answers, and the text of what its predicate
means (`consequenceText`). This module imports all of Lean, so a project that only writes records and
explanations need not import it.

Everything this module prints about who confirmed or answered something is words of
`LeanIntent.Settled`: `Restatement.words`, `Settled.words`, `Answerer.says` and `Answerer.title`,
each a function of the recorded status, whose theorems say what the words claim. The reader's
functions below read that
status from the explanation or the attributed answer by its constructors, and refuse any other term,
such as an `Answer` with no `Attributed` around it. So no path here names an owner or an answerer
except through the record, or words a caller gives (`Statuses.given`), but that the record is true is
not checked here: the rendering says so, and `LeanIntent.Confirmation` is what checks it.

The readable form (`Reader.print`) prints a term by Lean's own delaborator and formatter, and shows
the text only when Lean's parser and elaborator read it back as that term, binder names and metadata
aside, in the namespace the text names and with nothing opened (`elaboratesTo`), or, for a term that
holds a `match`, as one Lean's kernel finds definitionally equal to it, since each reading of a
`match` compiles a new constant. So a print that dropped a binder, a hypothesis or an argument Lean
does not infer back is never shown: it elaborates to another term or to none. When a print is not read back, a more explicit one is tried
(`readableOptions`), and last the exact form, which the audited printer's theorems cover; only what
neither form can print is refused. That the readable text is read back is checked each time, for
that term, and is no theorem. Notation declared outside Lean's own libraries is listed in the text
(`notationPart`), since the definitions it prints do not say what a notation means to a reader.

A generic explanation, a constant whose type has binders before `Explanation r`, is read at those
binders as local variables, so the rendering says what the record says for every value of them:
it lists them first (`paramsPart`) and prints each statement with them free, closing the statement
over them only in the exact form. `#render_intent_at` reads the same constant applied to values, so
each statement it shows is the generic one with the parameters replaced, and says what that instance
does not establish (`instanceNote`, citing `LeanIntent.Family`).

The declarations a meaning reaches are those `LeanIntent.Print.meaning` collects from the constants
the printed terms name (`LeanIntent.Cone.exprRefs`), by the relation the check that a record does
not depend on its implementation follows, as that check defines it (`LeanIntent.Cone.RefersTo`,
listed by `LeanIntent.Cone.declRefs`): the names each declaration's type mentions, a definition's
value, an inductive type's block, constructors and recursors, a constructor's inductive type, and a
recursor's block and rules, but not a theorem's proof or an opaque constant's value, which no term
that uses them depends on; except that a definition by structural or well-founded recursion is
followed through its type and the equation it is shown by, below, in place of its value
(`LeanIntent.Print.refsVia`); for the rendering, also lean-intent's `IntentRecord.Meets`, which says
what it is for a subject to meet the record, and, when it shows consequences, `Consequence.HoldsOf`,
which says what it is for one to hold as shown; for an answer, those of the record it answers and
`Answer.KeptBy`, which says what it asks of every later revision. `LeanIntent.Print.meaning_ok`
proves that it collects every declaration reached, and nothing else. The meaning stops at the
declarations of Lean's own libraries, whose modules the process's search path finds in those
libraries' directory (`leanOwnModules`), and the text records that release and its commit instead;
the definitions of lean-intent itself are printed like a project's. For an intent record, and an
answer to it, it also stops at the record's own constant, whose meaning is shown statement by
statement.

Each declaration collected is printed in full, or the text is refused (`declSection`): a
definition's type and value; a definition by structural or well-founded recursion, which Lean
compiles into a value its syntax cannot write, by its type and the equation Lean proves for it,
`c.eq_def`, which states its value at every argument and determines it; a theorem's, an opaque
constant's and an axiom of a proposition's type, which is all a term that uses one depends on; an
inductive type's type, its number of parameters and each constructor's type, which for a structure
lists its fields; a function that reads a field of a structure, whose value is checked to be the
projection Lean makes, by its type, the number of `fun`s of its value, its structure and its
field's index, which determine its value up to the names, types and annotations of those `fun`s
(`projShape_determines`), while for a well-typed definition its printed type fixes those types up
to definitional equality, which is argued, not proved. A constructor is printed with its inductive
type and a recursor is derived by Lean's kernel from its inductive types, so neither has a section
of its own once those are printed. An axiom whose type is not a proposition is refused, since in a
module of Lean's module system Lean shows an imported definition whose body is not exposed that
way, as is a name with no declaration and every type, value or equation the printer cannot print
or Lean does not read back. So no text prints a meaning in part.

A definition is shown by its equation exactly when Lean's own record of the definitions it compiled
by structural or by well-founded recursion holds it (`recursionKind`), and its equation is the one
Lean states for it (`Lean.Meta.getUnfoldEqnFor?`), of the form `∀ x₁ … xₙ, c x₁ … xₙ = r`
(`unfoldsTo`), resting with `c` on no axiom but Lean's own (`unfoldEqn`); otherwise it is refused,
naming it. The equation determines the definition: Lean accepts such a definition only when `r`
uses the values of `c`, and of any function defined together with it, only at arguments below
`x₁ … xₙ`, structural subterms or arguments below them by a well-founded relation its termination
proof shows, for `c` or any function in its place, so `r` computes each value from values below
it, and any two functions, or families of functions defined together, that satisfy such equations
are equal (`eq_of_recursion_eqn`, proved for one function of one argument). That Lean's equation
has that form is argued from how Lean compiles these definitions, not proved; that the termination
proof is a proof rests on the axiom check. A definition by `partial_fixpoint`, whose equation need
not determine it (for instance `f n = f (n + 1)`), and every other definition are printed by their
value, and refused when it cannot be printed, such as one that holds a projection. The printer
writes a `let` as `let` and one that does not depend on its value as `have`, as Lean reads them.

In the exact form, every term is printed by `LeanIntent.Print.print`, whose output `LeanIntent.Print.parse` reads back
as the very term printed, for every term (`LeanIntent.Print.parse_print`), after
`LeanIntent.Print.eraseMData` removes its metadata, which Lean documents as definitionally equal to
the term it annotates, and `LeanIntent.Print.canon` renames the binders whose names cannot be
written or would be misread, which changes nothing but those names
(`LeanIntent.Print.eraseNames_canon`). Before a printed term is shown, Lean itself must read it
back: Lean's parser and elaborator, in the root namespace with nothing opened, must elaborate the
printed text to the same term, binder names, which Lean's kernel ignores, and metadata aside. When
they do not, the text, a rendering or an answer's, is refused. So what the owner reads is what Lean
reads, for every term shown, though only as checked for that term and not as a theorem.

The rendering reads the explanation through Lean's own reduction to weak head normal form, so a
record, list or gloss built by any definition is read, as long as it reduces to its constructors;
a gloss must reduce to string literals. A statement is refused, and with it the rendering, when it
has free or meta variables, when the printer refuses it (`LeanIntent.Print.Printable` says which
terms it prints), when a part of its gloss is empty, or when Lean does not elaborate its printed
form back to it.

What is not proved: that the sections `declSection` writes print every part of a declaration, that
the equation a definition by recursion is shown by determines it, and that the document as a
whole, headings and prose included, determines what it prints, are argued from this module's code
and from how Lean compiles definitions, not stated as theorems; that a release's own libraries,
named with its version and commit, mean the same wherever that release runs is trusted with
Lean.
-/

namespace LeanIntent.Render

open Lean Meta Elab LeanIntent.Print
open LeanIntent.Cone (exprRefs)

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

/-- Whether `e` holds a `match`, by a constant Lean records as a matcher. -/
def holdsMatch (env : Environment) (e : Expr) : Bool :=
  (e.find? fun x => x.isConst && isMatcherCore env x.constName!).isSome

/-- Whether Lean's parser and elaborator read `text` as a term, in the namespace `ns` with nothing
opened, in the current local context and with the universe parameters of `e`, and elaborate it to
`e`, binder names and metadata aside. A term that holds a `match` may instead elaborate to one that
Lean's kernel finds definitionally equal to `e`: Lean compiles a `match` anew each time it reads one,
into a new auxiliary constant, so no reading of it is the same term. -/
def elaboratesTo (text : String) (e : Expr) (ns : Name := .anonymous) : MetaM Bool := do
  match Parser.runParserCategory (← getEnv) `term text with
  | .error _ => return false
  | .ok stx =>
    let lvls := (collectLevelParams {} e).params.toList
    withoutModifyingState do
      try
        let e' ← withTheReader Core.Context
            (fun ctx => { ctx with currNamespace := ns, openDecls := [] }) do
          Term.TermElabM.run' <| Term.withLevelNames lvls <| Term.withoutErrToSorry do
            let e' ← Term.elabTerm stx none
            Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e'
        if e'.hasMVar then return false
        if (eraseNames (eraseMData e')).equal (eraseNames e) then return true
        let env ← getEnv
        unless holdsMatch env e do return false
        return Kernel.isDefEqGuarded env (← getLCtx) e' e
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
      throwError "cannot print{indentExpr e}\nthe printer refuses it: it holds a projection, \
        a universe metavariable, or a name it cannot write"
    | some text =>
      if ← elaboratesTo text ec then return text
  throwError "cannot print{indentExpr e}\nLean does not elaborate its printed form back to it"

/-! ## The readable form -/

/-- The two forms a text prints a term in. -/
inductive Form where
  /-- With Lean's notation and without what Lean infers, read back by Lean. -/
  | readable
  /-- With every implicit argument, by the audited printer. -/
  | exact
  deriving BEq

/-- What fixes how Lean's delaborator prints, set whatever the options in force: Lean's notation,
no universes or implicit arguments, the types of `fun` binders, so that the text elaborates with no
expected type, and every proof and deep term in full, since an elided part could not be read back. -/
def baseOptions (o : Options) : Options :=
  let o := [(`pp.all, false), (`pp.notation, true), (`pp.explicit, false), (`pp.universes, false),
      (`pp.fullNames, false), (`pp.funBinderTypes, true), (`pp.piBinderTypes, true),
      (`pp.letVarTypes, true), (`pp.proofs, true), (`pp.deepTerms, true), (`pp.oneline, false),
      (`pp.mdata, false), (`pp.natLit, false), (`pp.numericTypes, false),
      (`pp.coercions, true), (`pp.fieldNotation, true), (`pp.structureInstances, true),
      (`pp.match, true), (`pp.beta, false), (`pp.tagAppFns, false), (`pp.exprSizes, false)].foldl
    (fun o (n, v) => o.setBool n v) o
  (o.set `pp.maxSteps (1000000 : Nat)).set `format.width (100 : Nat)

/-- The further options tried in turn, each more explicit, until Lean reads a print back: as is;
with the type of each numeral and structure instance; without the shorthand of field access,
coercions, structure instances and `match`; and with every implicit argument and universe. -/
def readableOptions : List (List (Name × Bool)) :=
  [[], [(`pp.numericTypes, true), (`pp.structureInstanceTypes, true)],
    [(`pp.numericTypes, true), (`pp.coercions, false), (`pp.fieldNotation, false),
      (`pp.structureInstances, false), (`pp.match, false)],
    [(`pp.explicit, true), (`pp.universes, true), (`pp.fieldNotation, false),
      (`pp.structureInstances, false), (`pp.match, false)]]

/-- What fixes how a text prints: its form, the namespace its terms are read in, the parameters of
a generic explanation, free in its terms; which imported modules are Lean's own; and the notation
found so far that is declared elsewhere. -/
structure Reader where
  /-- The form. -/
  form : Form
  /-- The namespace terms are read in, for the readable form. -/
  ns : Name := .anonymous
  /-- The parameters, local variables of the context the reader is used in. -/
  params : Array Expr := #[]
  /-- For each imported module, whether it is one of Lean's own libraries (`leanOwnModules`). -/
  own : Array Bool
  /-- The notation used that is declared outside Lean's own libraries. -/
  notations : IO.Ref NameSet

/-- `e` printed exactly, with the reader's parameters as `fun`s around it, which it may mention. -/
def Reader.printClosed (R : Reader) (e : Expr) : MetaM String := do
  printExact (← mkLambdaFVars R.params e)

/-- The names of syntax in `stx` declared outside Lean's own libraries. Each is the name Lean gave
the notation's parser, a declaration of the module that declares the notation. -/
def Reader.foreignKinds (R : Reader) (stx : Syntax) : MetaM NameSet := do
  let env ← getEnv
  let mut found : NameSet := {}
  for s in stx.topDown do
    let k := s.getKind
    if env.contains k then
      match env.getModuleIdxFor? k with
      | some idx => unless R.own[idx.toNat]?.getD false do found := found.insert k
      | none => found := found.insert k
  return found

/-- `e` printed by Lean's delaborator and formatter with the options `extra`, and the notation of
the print declared outside Lean's own libraries; the print is read in the reader's namespace. -/
def Reader.delabWith (R : Reader) (extra : List (Name × Bool)) (e : Expr) :
    MetaM (String × NameSet) := do
  withOptions (fun o => extra.foldl (fun o (n, v) => o.setBool n v) (baseOptions o)) do
    withTheReader Core.Context (fun ctx => { ctx with currNamespace := R.ns, openDecls := [] }) do
      let lctx := (← getLCtx).sanitizeNames.run' { options := (← getOptions) }
      Meta.withLCtx' lctx do
        let stx ← PrettyPrinter.delab e
        let text := (← PrettyPrinter.ppTerm stx).pretty 100
        return (text, ← R.foreignKinds stx)

/-- `e` as the reader's form prints it. The exact form prints it by `printExact`. The readable form
shows the first print of `readableOptions` that Lean reads back as `e`, binder names and metadata
aside, in the reader's namespace, and records its foreign notation; when none is read back, it
prints `e` as the exact form does. An error when `e` has what no term of the text can have. -/
def Reader.print (R : Reader) (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  if e.hasMVar || e.hasLooseBVars || (e.hasFVar && R.params.isEmpty) then
    throwError "cannot print{indentExpr e}\nas it has free or meta variables"
  if R.form == .exact then return ← R.printClosed e
  -- A binder keeps a parameter's name unless the term mentions that parameter.
  let locals ← R.params.toList.filterMapM fun x => do
    if e.containsFVar x.fvarId! then return some (← x.fvarId!.getDecl).userName else return none
  let ec := canon (constRoots e ++ locals) [] (eraseMData e)
  for extra in readableOptions do
    let attempt ← observing? (R.delabWith extra ec)
    if let some (text, kinds) := attempt then
      if ← elaboratesTo text ec R.ns then
        R.notations.modify (kinds.foldl .insert ·)
        return text
  R.printClosed e

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

/-- The name `e` reduces to, whose characters are checked again as an identifier's. -/
def readIdent (e : Expr) : MetaM Ident := do
  let s ← strLit (← ctorArgs e ``Word.mk 3)[1]!
  if h : s.toList ≠ [] ∧ s.toList.all identChar = true then return ⟨s, h⟩
  throwError "expected a name of the owners' log, found {repr s}"

/-- The verdict `e` reduces to. -/
def readVerdict (e : Expr) : MetaM Verdict := do
  let e ← whnf e
  if e.isConstOf ``Verdict.confirmed then return .confirmed
  if e.isConstOf ``Verdict.declined then return .declined
  throwError "expected a verdict, found{indentExpr e}"

/-- The answerer `e` reduces to; refused when a decision on the owner's behalf gives no reason. -/
def readAnswerer (e : Expr) : MetaM Answerer := do
  let e ← whnf e
  if e.isAppOfArity ``Answerer.owner 1 then
    return .owner (← readIdent e.appArg!)
  if e.isAppOfArity ``Answerer.onBehalf 3 then
    let a := e.getAppArgs
    let reason ← strLit a[2]!
    if reason.trimAscii.isEmpty then
      throwError "the decision on the owner's behalf by{indentExpr a[0]!}\ngives no reason"
    return .onBehalf (← readIdent a[0]!) (← readIdent a[1]!) reason
  throwError "expected who gave an answer, found{indentExpr e}"

/-- The standing of the record's restatement that `e` reduces to. -/
def readRestatement (e : Expr) : MetaM Restatement := do
  let e ← whnf e
  if e.isConstOf ``Restatement.unconfirmed then return .unconfirmed
  if e.isAppOfArity ``Restatement.confirmed 1 then return .confirmed (← readIdent e.appArg!)
  throwError "expected whether a restatement is confirmed, found{indentExpr e}"

/-- A consequence recorded as derived, of a record whose restatement stands as `s`. -/
def readDerived : (s : Restatement) → MetaM (Settled s)
  | .confirmed _ => return .derived
  | .unconfirmed => throwError "a consequence of a record whose restatement no owner confirmed is \
      recorded as derived from it"

/-- The status `e` reduces to, of a consequence of a record whose restatement stands as `s`. -/
def readSettled (s : Restatement) (e : Expr) : MetaM (Settled s) := do
  let e ← whnf e
  if e.isAppOfArity ``Settled.answered 3 then
    let a := e.getAppArgs
    return .answered (← readAnswerer a[1]!) (← readVerdict a[2]!)
  if e.isAppOfArity ``Settled.fork 1 then return .fork
  if e.isAppOfArity ``Settled.unsettled 1 then return .unsettled
  if e.isAppOfArity ``Settled.derived 1 then return ← readDerived s
  throwError "expected who settled a consequence, found{indentExpr e}"

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

/-- A statement: its heading, its exact print, then any lines `settled` before its gloss. -/
def statement (heading text : String) (gloss : Array String) (settled : String := "") : String :=
  s!"### {heading}\n\n{code text}\n{settled}- **Requires:** {gloss[0]!}\n\
    - **Rules out:** {gloss[1]!}\n- **Still allows:** {gloss[2]!}\n\
    - **Freedom O5 leaves:** {gloss[3]!}\n\n"

/-! ## The declarations a meaning reaches -/

/-- The first components of the names of the modules of Lean's own libraries. -/
def leanRoots : List Name := [`Init, `Std, `Lean, `Lake]

/-- Whether the module `m`, whose `.olean` file has the real path `real?` if it has one, is one of
Lean's own libraries, whose directory has the components `lib`: the first component of its name is
one of `leanRoots`, and its file really lies in that directory. Its arguments are all it reads, so
it takes nothing from where the running executable lies (`isLeanOwn_iff`). -/
def isLeanOwn (lib : List String) (m : Name) (real? : Option System.FilePath) : Bool :=
  leanRoots.contains m.getRoot && real?.any fun p => lib.isPrefixOf p.components

/-- A module is one of Lean's own libraries exactly when it has the first component of one of their
names and its file really lies in their directory. So a project's module that merely shares such a
name is not, wherever its name would place it, and neither is one with no file. -/
theorem isLeanOwn_iff {lib : List String} {m : Name} {real? : Option System.FilePath} :
    isLeanOwn lib m real? = true ↔
      m.getRoot ∈ leanRoots ∧ ∃ p, real? = some p ∧ lib <+: p.components := by
  cases real? <;> simp [isLeanOwn]

/-- The real path of the `.olean` file the process's search path (`Lean.searchPathRef`) gives the
module `m`, when that file exists. Lean resolves an import through the same path
(`Lean.findOLean`), and starts no process to do so. -/
def realOLean? (m : Name) : IO (Option System.FilePath) := do
  (← (← searchPathRef.get).findModuleWithExt "olean" m).mapM IO.FS.realPath

/-- The real path of the directory of Lean's own libraries, read from the process's search path and
never from where the running executable lies, which is the toolchain only in the `lean` binary
(`Lean.getBuildDir`): the directory that really holds the `.olean` file the search path gives
`Init.Prelude`, the module that declares what all else rests on, and that also really holds the root
file of each library. So a toolchain copied elsewhere is found where the search path has it, and
modules of a project that shadow `Init` with links to the toolchain, or `Init` itself, do not move
it. An error, never an empty set of modules, when there is no such directory: a process that has
set no search path, or whose path gives `Init.Prelude` no such file. -/
def leanLibDir : IO System.FilePath := do
  let refuse {α} (why : String) : IO α := throw <| IO.userError
    s!"cannot find Lean's own libraries from the search path: {why}. The process must set its search \
      path (Lean.initSearchPath, or Lean.searchPathRef) to the one it imports the project through"
  let some prelude ← realOLean? `Init.Prelude
    | refuse "it gives Init.Prelude no file"
  let some lib := prelude.parent >>= (·.parent)
    | refuse s!"{prelude} has no parent directory"
  for root in leanRoots do
    let file := modToFilePath lib root "olean"
    unless ← file.pathExists do
      refuse s!"{lib}, which holds Init.Prelude, has no {file.fileName.getD ""}"
    unless (← IO.FS.realPath file).parent == some lib do
      refuse s!"{file}, beside the Init.Prelude it gives, is a link to another directory"
  return lib

/-- For each module the environment imports, whether it is one of Lean's own libraries (`isLeanOwn`,
in the directory `leanLibDir` finds), asking the file system only of a module whose name could be.
A module of a project that merely shares one of those names is not. An error when the process
cannot establish where those libraries are. -/
def leanOwnModules : MetaM (Array Bool) := do
  let lib := (← leanLibDir).components
  (← getEnv).header.moduleNames.mapM fun m => do
    return isLeanOwn lib m (← if leanRoots.contains m.getRoot then realOLean? m else pure none)

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

/-- The part `part` of the declaration `c`, `e`, printed by the reader; an error naming both when
it cannot be. -/
def printPart (R : Reader) (c : Name) (part : String) (e : Expr) : MetaM String := do
  try R.print e
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

section Recursion

universe u v

/-- **The equation of a well-founded recursion determines its solution.** When `r` is well-founded
and `F` computes a value at `x` from values at the arguments `r`-below `x`, any two functions that
both satisfy `f x = F x (fun y _ => f y)` at every `x` are equal. The equation Lean proves for a
definition by structural or well-founded recursion, read as a property of the function it names,
has this form, which is argued in `declSection`, not proved. -/
theorem eq_of_recursion_eqn {α : Sort u} {β : α → Sort v} {r : α → α → Prop} (hr : WellFounded r)
    (F : (x : α) → ((y : α) → r y x → β y) → β x) {f g : (x : α) → β x}
    (hf : ∀ x, f x = F x fun y _ => f y) (hg : ∀ x, g x = F x fun y _ => g y) : f = g :=
  funext fun x => hr.induction (C := fun x => f x = g x) x fun x ih => by
    rw [hf x, hg x]
    congr 1
    funext y h
    exact ih y h

end Recursion

/-- How Lean compiled the definition `c`: `some true` when its own record of the definitions it
compiled by structural recursion (`Lean.Elab.Structural.eqnInfoExt`) holds `c`, `some false` when its
record of those it compiled by well-founded recursion (`Lean.Elab.WF.eqnInfoExt`) does, each read as
Lean reads it to state `c`'s unfolding equation, and `none` otherwise. A definition by
`partial_fixpoint`, whose equation need not determine it, is in neither, and is printed by its
value. -/
def recursionKind (env : Environment) (c : Name) : Option Bool :=
  if (Elab.Structural.eqnInfoExt.find? env c).isSome then some true
  else if (Elab.WF.eqnInfoExt.find? env c).isSome then some false
  else none

/-- Whether `t` is `∀ x₁ … xₙ, c x₁ … xₙ = r`, after the `k` binders already passed, for some `n`
and `r`, where `c` is the constant `c` at the universe levels `us`: an equation that states the value
of `c` at every argument. -/
def unfoldsTo (c : Name) (us : List Level) : Nat → Expr → Bool
  | k, .forallE _ _ b _ => unfoldsTo c us (k + 1) b
  | k, e => e.isAppOfArity ``Eq 3 &&
      e.appFn!.appArg! == mkAppN (.const c us) ((List.range k).reverse.map Expr.bvar).toArray

/-- The equation Lean proves for the definition `c` by recursion (`Lean.Meta.getUnfoldEqnFor?`),
`c.eq_def`, and its statement, `∀ x₁ … xₙ, c x₁ … xₙ = r`, with the universe parameters `levels`
of `c`. An error, naming `c`, when Lean gives none, when its statement or universe parameters are
not those, or when it rests on an axiom other than Lean's own (`LeanIntent.Cone.leanAxioms`): since
its statement names `c`, the axioms of `c`, its termination proof among them, are among its own
(`Lean.collectAxioms` follows each constant's type and value). -/
def unfoldEqn (c : Name) (levels : List Name) : MetaM (Name × Expr) := do
  let eq? ← try getUnfoldEqnFor? c (nonRec := false)
    catch err => throwError "cannot print {c}: Lean cannot state its equation: {err.toMessageData}"
  let some eq := eq?
    | throwError "cannot print {c}: Lean gives no equation that unfolds it"
  let some eci := ((← getEnv).setExporting false).find? eq
    | throwError "cannot print {c}: its equation {eq} has no declaration here"
  unless eci.levelParams == levels && unfoldsTo c (levels.map .param) 0 eci.type do
    throwError "cannot print {c}: its equation {eq} does not state its value at every argument"
  let axs ← collectAxioms eq
  unless axs.all LeanIntent.Cone.leanAxioms.contains do
    throwError "cannot print {c}: it or its equation {eq} rests on the axioms {axs.toList}, not \
      only on Lean's own, so its termination proof, if any, may not be one"
  return (eq, eci.type)

/-- The section that prints the declaration `ci`, named `c`, in full, from the declarations `out`
that `LeanIntent.Print.meaning` collected; `none` for a constructor, printed with its inductive
type, and for a recursor, which Lean's kernel derives from its inductive types, when `out` holds
those; an error, naming what cannot be printed, otherwise. A function that reads a field of a
structure is printed by its type and its description by `projectionOf`, which determines its value
up to the names, types and annotations of its leading `fun`s (`projShape_determines`); for a
well-typed definition, its printed type fixes those types up to definitional equality, which is
argued, not proved.

A definition by structural or well-founded recursion, which `eqns` gives an equation for
(`unfoldEqn`), is printed by its type and that equation, `∀ x₁ … xₙ, c x₁ … xₙ = r`, in place of its
value. The equation determines `c`, which is argued, not proved: Lean accepts such a definition only
when `r` uses the values of `c`, and of any function defined together with it, only at arguments
below `x₁ … xₙ` by a well-founded relation, structural subterms or a measure its termination proof
shows decreases, for `c` or any function in its place, so `r` computes the value at `x₁ … xₙ` from
values below them; and two functions, or families of functions defined together, that both satisfy
such equations are equal (`eq_of_recursion_eqn`, for one function of one argument). The relation is
well-founded because the termination proof rests on no axiom but Lean's own, which `unfoldEqn`
checks. -/
def declSection (R : Reader) (lookup : Name → Option ConstantInfo)
    (out : List (Name × ConstantInfo)) (eqns : NameMap (Name × Expr)) (c : Name)
    (ci : ConstantInfo) : MetaM (Option String) := do
  let has (n : Name) : Bool := out.any (·.1 == n)
  match ci with
  | .ctorInfo v =>
    unless has v.induct do throwError "cannot print {c}: its inductive type is not printed"
    return none
  | .recInfo v =>
    unless v.all.all has do throwError "cannot print {c}: its inductive types are not printed"
    return none
  | _ => pure ()
  let type ← printPart R c "type" ci.type
  let head (words : String) :=
    s!"### {c}\n\n{words}. It has {univWords ci.levelParams}. Its type:\n\n{code type}\n"
  match ci with
  | .ctorInfo _ | .recInfo _ => return none
  | .defnInfo v =>
    if let some (eq, t) := eqns.find? c then
      let (kind, shows, below) := if recursionKind (← getEnv) c == some true then
          ("structural recursion", "", "at structural subterms of the arguments it recurses on")
        else ("well-founded recursion", "its termination proof shows that ",
          "at arguments below those on the left by a well-founded relation")
      return some (head s!"A definition by {kind}" ++ s!"Its value is not printed: Lean \
        compiles a definition by recursion into a term its syntax cannot write. In its place is \
        the equation Lean proves for it, `{eq}`, which Lean's kernel checked, stating its value at \
        every argument:\n\n{code (← printPart R c "equation" t)}\nThe equation determines {c}: Lean \
        accepts a definition by {kind} only when {shows}the right of the equation uses the values \
        of {c}, and of any function defined together with it, only {below}, so only one \
        function, or family of functions defined together, satisfies their equations. {c} and \
        its equation rest on no axiom but Lean's own.\n\n")
    match projectionOf lookup v with
    | some (n, s, i) =>
      return some (head s!"A function that reads a field of a structure: its value is `fun` over \
        its first {n} arguments and returns field number {i + 1}, counted after the parameters in \
        the type of {s}'s constructor, of its argument number {n}, a value of {s}")
    | none =>
      let value ← printPart R c "value" v.value
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
      | some (.ctorInfo kv) => s := s ++ s!"#### {k}\n\n{code (← printPart R k "type" kv.type)}\n"
      | _ => throwError "cannot print {c}: its constructor {k} has no declaration here"
    return some s

/-- The toolchain the rendering is made with, whose libraries are not printed. -/
def toolchain : String :=
  s!"## Lean's own libraries\n\nThe declarations of Lean's own libraries (Init, Std, Lean and \
    Lake) are not printed: they are those of Lean {Lean.versionString}, commit {Lean.githash}, \
    which made this text. A declaration is counted as Lean's own when Lean found the module that \
    declares it in that release's library directory.\n"

/-- Every declaration the constants `roots` reach (`LeanIntent.Print.meaning`), outside Lean's own
libraries and `shown`, printed in full by `declSection` in the reader's form, in the order they are
reached; an error, naming what cannot be printed, when one cannot be, so nothing is printed in part.
In the readable form, the code Lean generated for each `match` and lean-intent's own declarations,
the same in every text, come last, folded, so that a reader can tell a project's definitions from
them. A definition by
recursion (`recursionKind`) reaches what its type and its equation (`unfoldEqn`) mention, in place
of what its value does: each pass collects the meaning with the equations found so far, following
nothing from a definition by recursion whose equation is not yet found, and then finds those; the
pass that finds none to add is the one printed, so every definition by recursion it reaches is
followed through its equation. Each pass but the last adds the equation of a declaration of the
environment, so there are finitely many. -/
def definitions (R : Reader) (roots : List Name) (shown : NameSet) : MetaM String := do
  let own := R.own
  let mut eqns : NameMap (Name × Expr) := {}
  repeat
    -- Finding an equation may add declarations, so each pass reads the environment anew.
    let env ← getEnv
    let lookup := fun c => (env.setExporting false).find? c
    let stop := stopAt env own shown
    let found := eqns
    -- `Prop` mentions no name: a definition by recursion whose equation is not yet found is
    -- followed through its type alone in this pass.
    let eqn := fun c => match found.find? c with
      | some (_, t) => some t
      | none => if (recursionKind env c).isSome then some (.sort .zero) else none
    let out ← match meaning lookup eqn stop roots with
      | .ok out => pure out
      | .error (.unknown c) => throwError "cannot print {c}: it has no declaration here"
      | .error .fuel => throwError "cannot print the definitions: there are too many"
    let todo := out.filter fun (c, ci) =>
      ci matches .defnInfo _ && (recursionKind env c).isSome && !found.contains c
    if todo.isEmpty then
      let isLibrary (c : Name) : Bool := R.form == .readable &&
        match env.getModuleIdxFor? c with
        | some idx => (env.header.moduleNames[idx.toNat]?.map Name.getRoot) == some `LeanIntent
        | none => false
      let isGenerated (c : Name) : Bool := R.form == .readable &&
        (isMatcherCore env c || isCasesOnRecursor env c)
      let mut text := ""
      let mut generated := ""
      let mut library := ""
      for (c, ci) in out do
        if let some s ← declSection R lookup out found c ci then
          if isLibrary c then library := library ++ s
          else if isGenerated c then generated := generated ++ s
          else text := text ++ s
      let folded (heading words body : String) : String :=
        if body.isEmpty then "" else s!"## {heading}\n\n{words} They are folded, not left out.\n\n\
          <details>\n<summary>Each of them, printed in full</summary>\n\n{body}</details>\n\n"
      return text ++ folded "The code Lean generated for each `match`" "Lean compiles each `match` \
          into these; the definitions above show the `match` as Lean reads it." generated ++
        folded "lean-intent's own definitions" "These say what a record is and what it is to meet \
          one, the same in every rendering that reaches them." library
    for (c, ci) in todo do
      eqns := eqns.insert c (← unfoldEqn c ci.levelParams)
  throwError "unreachable: the loop returns when no equation is left to find"

/-- The kind of a consequence, `e` reduced to its constructor, and what it is shown as. -/
def kindWords (e : Expr) : MetaM (Expr × String) := do
  let kind ← whnf e
  if kind.isConstOf ``Consequence.Kind.entailment then
    return (kind, "an entailment: every subject that meets the record satisfies it")
  else if kind.isConstOf ``Consequence.Kind.possibility then
    return (kind, "a possibility: some subject that meets the record satisfies it")
  else throwError "expected the kind of a consequence, found{indentExpr kind}"

/-- How a text says its statements are printed, in the reader's form. -/
def formWords (R : Reader) : String :=
  match R.form with
  | .exact => "Each statement is printed exactly: as Lean syntax that Lean elaborates back to the \
      term its kernel checks, binder names and metadata aside, from the root namespace with \
      nothing opened."
  | .readable =>
    let where_ := if R.ns.isAnonymous then "from the root namespace" else s!"in the namespace {R.ns}"
    s!"Each statement is printed with Lean's notation, leaving out what Lean infers: as Lean syntax \
      that Lean elaborates back to the term its kernel checks, binder names and metadata aside, \
      {where_} with nothing opened. Where Lean does not read a shorter print back, a more explicit \
      one is shown, and last the exact form, read from the root namespace with nothing opened."

/-- What a text says of a record shown at particular values: that it speaks of those values, and
what they do not establish of the family they come from, `f`. -/
def instanceNote (f : Name) : String :=
  s!"These are the statements of {f} with its parameters replaced by these values, read from {f} \
    applied to them, and they speak of these values only. An obligation proved here shows only that \
    some parameter has it (`{``LeanIntent.Family.exists_of_at}`), a failure here refutes a generic \
    claim whose condition admits these values (`{``LeanIntent.Family.not_holdsWhere_of_at}`), and \
    an instance alone does not in general prove an obligation of a family: \
    `{``LeanIntent.Family.not_generic}` gives, for each, a family of which it holds at \
    one parameter and fails at another.\n\n"

/-- One binder of a generic explanation, `x`, written as a binder is, by the reader. -/
def binderText (R : Reader) (x : Expr) : MetaM String := do
  let d ← x.fvarId!.getDecl
  let type ← R.print d.type
  let (l, r) := match d.binderInfo with
    | .default => ("(", ")")
    | .implicit => ("{", "}")
    | .strictImplicit => ("⦃", "⦄")
    | .instImplicit => ("[", "]")
  let name := d.userName
  if d.binderInfo.isInstImplicit && name.hasMacroScopes then return s!"{l}{type}{r}"
  return s!"{l}{name.eraseMacroScopes} : {type}{r}"

/-- The section of a generic explanation that lists its parameters; nothing when it has none. -/
def paramsPart (R : Reader) : MetaM String := do
  if R.params.isEmpty then return ""
  let lines ← R.params.mapM (binderText R)
  return s!"## Parameters\n\nThis record is generic. Every statement below is about every value \
    of these parameters, which appear in it as variables:\n\n{code ("\n".intercalate lines.toList)}\n"

/-- What a rendering says of who settled each thing. -/
inductive Statuses where
  /-- What the explanation holds, which is a value its project writes. -/
  | recorded
  /-- Nothing: the text an answer is recorded against, which recording the answer must not change. -/
  | omitted
  /-- These words for the restatement, and for each consequence in order, which a caller has
  checked. -/
  | given (restatement : String) (consequences : Array String)

/-- The rendering of the explanation `exTerm`, a term of type `LeanIntent.Explanation r`, up to its
definitions: what `statuses` says of whether an owner confirmed the record's restatement, the
record's shape and statements, and the consequences shown with what `statuses` says of who settled
each, each printed by the reader with its gloss; with the constants the record's meaning starts from,
and the record's own constant, at which it stops, since each of its statements is shown. `note` says
what the record's values are, when they need saying. -/
def recordPart (R : Reader) (exTerm : Expr) (note : String := "") (statuses : Statuses := .recorded) :
    MetaM (String × List Name × NameSet) := do
  let ex ← ctorArgs exTerm ``Explanation.mk 11
  let r ← ctorArgs ex[1]! ``IntentRecord.mk 5
  let restatement ← readRestatement ex[6]!
  -- A record that is a family applied to values speaks of those values, however it was reached.
  let note := match ex[1]!.getAppFn with
    | .const f _ =>
      if note.isEmpty && R.form == Form.readable && R.params.isEmpty && ex[1]!.isApp &&
          f != ``IntentRecord.mk then instanceNote f else note
    | _ => note
  let confirmedPart (intro words : String) : String × String :=
    (s!" {intro}", s!"## Whether an owner confirmed this restatement\n\n{words}\n")
  let (standing, confirmed) := match statuses with
    | .recorded => confirmedPart "Who settled each thing is printed as this record holds it; \
        `LeanIntent.Trace` decides, from a project's owners' log, whether an answer's authority \
        traces back to a declared owner, and this document does not."
        (String.ofList restatement.words)
    | .omitted => ("", "")
    | .given words _ => confirmedPart "Who settled each thing is printed as the project's owners' \
        log holds it for this revision." words
  let mut doc := s!"# The intent record {← R.print ex[1]!}\n\n{formWords R} The plain words after \
    it are written by a model and are trusted, not proved.{standing}\n\n{note}\
    {← paramsPart R}{confirmed}## Shape\n\n"
  let mut printed : Array Expr := #[ex[1]!]
  for x in R.params do
    printed := printed.push (← x.fvarId!.getDecl).type
  doc := doc ++ statement "The subject" (← R.print r[1]!) (← readGloss ex[2]!)
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
        let heading := s!"{← strLit a[0]!}, a predicate over `{← R.print a[1]!}`"
        doc := doc ++ statement heading (← R.print a[2]!) (← readGloss gloss)
        printed := printed ++ #[a[1]!, a[2]!]
      else
        doc := doc ++ statement (← strLit a[1]!) (← R.print a[2]!) (← readGloss gloss)
        printed := printed.push a[2]!
  doc := doc ++ match statuses with
    | .omitted => "## Consequences\n\n"
    | _ => "## Consequences, each with who settled it\n\n"
  let consequences ← listElems ex[7]!
  if consequences.isEmpty then doc := doc ++ "None.\n\n"
  if let .given _ words := statuses then
    unless words.size == consequences.size do
      throwError "{consequences.size} consequences and words for {words.size}"
  for h : i in [:consequences.size] do
    let shown := consequences[i]
    let s ← ctorArgs shown ``Shown.mk 7
    let c ← ctorArgs s[3]! ``Consequence.mk 4
    let (_, shownAs) ← kindWords c[2]!
    let settled ← match statuses with
      | .recorded => pure s!"- **Settled:** {String.ofList (← readSettled restatement s[6]!).words}"
      | .omitted => pure ""
      | .given _ words => pure s!"- **Settled:** {words[i]!}"
    doc := doc ++ statement s!"{← strLit c[1]!}, {shownAs}" (← R.print c[3]!) (← readGloss s[5]!)
      settled
    printed := printed.push c[3]!
  -- The record's own constant is the record shown above, statement by statement. What it means for
  -- a subject to meet the record, and for a consequence to hold of it as shown, are lean-intent's
  -- definitions, printed with the rest.
  let shown : NameSet := if let .const c _ := ex[1]!.getAppFn then ({} : NameSet).insert c else {}
  let roots := printed.toList.flatMap (exprRefs · []) ++ [``IntentRecord.Meets] ++
    if consequences.isEmpty then [] else [``Consequence.HoldsOf]
  return (doc, roots, shown)

/-- The section that lists the notation a text uses declared outside Lean's own libraries, which
none of its definitions says the meaning of to a reader; nothing when it uses none. -/
def notationPart (R : Reader) : MetaM String := do
  let kinds := (← R.notations.get).toList
  if kinds.isEmpty then return ""
  let env ← getEnv
  let lines := kinds.map fun k =>
    match env.getModuleIdxFor? k with
    | some idx => s!"- `{k}`, declared in {env.header.moduleNames[idx.toNat]!}\n"
    | none => s!"- `{k}`, declared in the file that made this text\n"
  return s!"## Notation from outside Lean's own libraries\n\nThe statements above use this notation, \
    whose declaration this text does not print. Lean read each statement back as the term its \
    kernel checks, so the notation changes nothing Lean checks; what it means to a reader is in its \
    source, and the exact form of this text (`#render_intent_exact`) prints each statement without \
    it.\n\n{String.join lines}\n"

/-- The sections of a text after its record part: every declaration its meaning reaches, under a
heading that says what they are, the notation it uses declared outside Lean's own libraries, and the
toolchain. -/
def definitionsPart (R : Reader) (roots : List Name) (shown : NameSet) : MetaM String := do
  return s!"## Definitions the record's meaning reaches\n\nThese are not statements of the \
    record: each is a declaration that a statement above depends on, or that says what it is for \
    a subject to meet the record and for a consequence to hold of it as shown, with everything \
    those depend on in turn. Each is printed in full: its type, a definition's value, or for a \
    definition by structural or well-founded recursion the equation that determines it, and an \
    inductive type's constructors, which for a structure are its fields; a theorem's proof and an \
    opaque constant's value are not, since no term that uses them depends on more than their \
    types. Their plain words are those of the statements that use them.\n\n\
    {← definitions { R with params := #[] } roots shown}{← notationPart R}{toolchain}"

/-- A new reader of the form `form` for the terms of the explanation `decl`, in its namespace. -/
def newReader (decl : Name) (form : Form) (params : Array Expr := #[]) : MetaM Reader := do
  return { form, ns := if form == .exact then .anonymous else decl.getPrefix, params,
           own := ← leanOwnModules, notations := ← IO.mkRef {} }

/-- The rendering of the explanation `decl`, in the form `form`: its record part (`recordPart`),
saying what `statuses` says of who settled each thing, every declaration that part's meaning reaches,
and the toolchain. `decl` is a constant of type
`LeanIntent.Explanation r`, or of a type with binders before that, a generic explanation, whose
binders are the parameters of the text: each statement is printed with them free, and its meaning
starts also from what their types mention. -/
def renderExplanation (decl : Name) (form : Form := .readable) (statuses : Statuses := .recorded) :
    MetaM String := do
  let ci ← getConstInfo decl
  let us := ci.levelParams.map Level.param
  let reader ← newReader decl form
  let (doc, roots, shown) ← forallTelescope ci.type fun params _ =>
    recordPart { reader with params } (mkAppN (mkConst decl us) params) (statuses := statuses)
  return doc ++ (← definitionsPart reader roots shown)

/-- The rendering of the generic explanation `decl` at the representative values `args`, one for
each of its binders, in the readable form: each statement is read from `decl` applied to `args`, so
it is the generic statement with the parameters replaced, and the text lists the values and says
what they do not establish of the generic record (`instanceNote`). A value that is a proof is shown
by the proposition it proves, since no term depends on more than its statement. The meaning starts
also from each term the list prints, so the definitions a value or a proposition reaches are
printed. -/
def renderAt (decl : Name) (us : List Level) (args : Array Expr) : MetaM String := do
  let ci ← getConstInfo decl
  let reader ← newReader decl .readable
  let binders ← forallBoundedTelescope (ci.type.instantiateLevelParams ci.levelParams us) args.size
    fun params _ => do
      unless params.size == args.size do
        throwError "{decl} takes {params.size} parameters here, and was given {args.size}"
      params.mapM fun x => return (← x.fvarId!.getDecl).userName.eraseMacroScopes
  let mut lines : Array String := #[]
  let mut roots : List Name := []
  for (name, a) in binders.zip args do
    let proof ← isProof a
    let term ← instantiateMVars (← if proof then inferType a else pure a)
    let printed ← reader.print term
    lines := lines.push <|
      if proof then s!"{name} : a proof of {printed}" else s!"{name} := {printed}"
    roots := exprRefs term roots
  let values := s!"## Representative values\n\nThis record is generic, and this text shows it at \
    these values of its parameters:\n\n{code ("\n".intercalate lines.toList)}\n{instanceNote decl}"
  let (doc, rootsDoc, shown) ← recordPart reader (mkAppN (mkConst decl us) args) values
  return doc ++ (← definitionsPart reader (rootsDoc ++ roots) shown)

/-! ## The texts an answer is recorded against -/

/-- The text of the revision the explanation `decl` shows: its rendering in the exact form, whose text
determines the term, saying nothing of who settled what, since recording an answer changes that and
must not change what the answer names. -/
def revisionText (decl : Name) : MetaM String :=
  renderExplanation decl .exact .omitted

/-- The canonical text of what the consequence with the predicate `pred` means: the predicate printed
exactly; every declaration it reaches, and `LeanIntent.Answer.KeptBy`, which says what an answer to
it asks of every later revision, each printed in full by `definitions`; and the toolchain. It does
not stop at the record, so a predicate stated through a record prints the record's value and
changes with it. An error, naming what cannot be printed, when any of it cannot be. -/
def consequenceText (pred : Expr) : MetaM String := do
  return s!"# A consequence's predicate\n\nPrinted exactly: as Lean syntax that Lean elaborates back \
    to the term its kernel checks, binder names and metadata aside, from the root namespace with \
    nothing opened.\n\n{code (← printExact pred)}\n## Definitions the predicate reaches\n\nEach \
    is printed in full, as in the rendering of a record, with what an answer to it asks of every \
    later revision (`LeanIntent.Answer.KeptBy`).\n\n\
    {← definitions (← newReader .anonymous .exact) (exprRefs pred [] ++ [``Answer.KeptBy]) {}}\
    {toolchain}"

/-! ## The answers -/

/-- The canonical text of the attributed answer `a`, a term of type `LeanIntent.Attributed W`, to
the explanation `ex`, a constant of type `LeanIntent.Explanation r`: who gave it
(`Answerer.title`, `Answerer.says`), and the answer printed exactly, with its consequence's name,
kind and predicate and its verdict, each reduced to its constructor or literal; then the name of
`ex` and its record part (`recordPart`), the record's statements and the consequences shown, as the
exact form prints them; then every declaration the record part and the
answer reach, `LeanIntent.Answer.KeptBy`'s among them, which says what the answer asks of every
later revision, each printed in full by one call of `definitions`; and the toolchain. An error,
naming what cannot be printed, when any of it cannot be. -/
def answerText (ex : Name) (a : Expr) : MetaM String := do
  let attributed ← ctorArgs a ``Attributed.mk 3
  let answerer ← readAnswerer attributed[2]!
  let ans ← ctorArgs attributed[1]! ``Answer.mk 3
  let c ← ctorArgs ans[1]! ``Consequence.mk 4
  let aus := (← whnf attributed[1]!).getAppFn.constLevels!
  let cus := (← whnf ans[1]!).getAppFn.constLevels!
  let name ← whnf c[1]!
  unless name matches .lit (.strVal _) do
    throwError "expected a string literal, found{indentExpr name}"
  let (kind, shownAs) ← kindWords c[2]!
  let verdict ← whnf ans[2]!
  let attribution := answerer.says (← readVerdict verdict)
  let term := mkApp3 (.const ``Answer.mk aus) ans[0]!
    (mkApp4 (.const ``Consequence.mk cus) c[0]! name kind c[3]!) verdict
  let answer := s!"# {answerer.title}\n\n{String.ofList attribution}\nThe consequence \
    answered is {repr (← strLit name)}, shown as {shownAs}. Who gave the answer is printed as this \
    record holds it; `LeanIntent.Trace` decides, from a project's owners' log, whether its \
    authority traces back to a declared owner, and this document does not. The answer, printed \
    exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names \
    and metadata aside, from the root namespace with nothing opened.\n\n\
    {code (← printExact term)}\n"
  let exConst := mkConst ex ((← getConstInfo ex).levelParams.map .param)
  let explained := s!"# The explanation it answers\n\nThe answer is given to the explanation \
    below, printed exactly, whose record and consequences follow as the exact form of its \
    rendering prints them.\n\n{code (← printExact exConst)}\n"
  let reader ← newReader ex .exact
  let (record, roots, shown) ← recordPart reader exConst
  return answer ++ explained ++ record ++ s!"## Definitions the answer and the record reach\n\n\
    These are not statements of the record or of the answer: each is a declaration that the \
    answer or a statement above depends on, or that says what it is for a subject to meet the \
    record, for a consequence to hold of it as shown, and what the answer asks of every later \
    revision of the record (`LeanIntent.Answer.KeptBy`), with everything those depend on in turn, \
    each printed in full as in the exact form of the rendering of a record.\n\n\
    {← definitions reader (roots ++ exprRefs term [] ++ [``Answer.KeptBy]) shown}{toolchain}"

/-- The canonical text of each attributed answer of the list `e` to the explanation `ex`
(`answerText`). -/
def answerTexts (ex : Name) (e : Expr) : MetaM (Array String) := do
  (← listElems e).mapM (answerText ex)

/-- `#render_intent e` shows the rendering of the explanation `e`. -/
syntax (name := renderIntent) "#render_intent " ident : command

@[command_elab renderIntent]
def elabRenderIntent : Command.CommandElab := fun stx => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  logInfo (← Command.liftTermElabM <| renderExplanation decl)

/-- `#render_intent_exact e` shows the rendering of the explanation `e` in the exact form: with every
implicit argument, by the audited printer. -/
syntax (name := renderIntentExact) "#render_intent_exact " ident : command

@[command_elab renderIntentExact]
def elabRenderIntentExact : Command.CommandElab := fun stx => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  logInfo (← Command.liftTermElabM <| renderExplanation decl .exact)

/-- `#render_intent_at e a₁ … aₙ` shows the rendering of the generic explanation `e` at the
representative values `a₁ … aₙ`, written as the arguments of an application of `e`, with what they do
not establish of the generic record. -/
syntax (name := renderIntentAt) "#render_intent_at " ident (ppSpace colGt term:max)+ : command

@[command_elab renderIntentAt]
def elabRenderIntentAt : Command.CommandElab := fun stx => do
  let f := stx[1]
  let args : Array Syntax := stx[2].getArgs
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  let text ← Command.liftTermElabM do
    let e ← Term.withoutErrToSorry <| Term.elabTerm (Syntax.mkApp ⟨f⟩ (args.map (⟨·⟩))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasMVar || e.hasFVar then
      throwError "the values must determine every parameter:{indentExpr e}"
    let .const c us := e.getAppFn
      | throwError "expected {decl} applied to values, found{indentExpr e}"
    unless c == decl do throwError "expected {decl} applied to values, found{indentExpr e}"
    renderAt decl us e.getAppArgs
  logInfo text

/-- `#answer_texts ex e` shows the canonical text of each attributed answer of the list `e` to the
explanation `ex`. -/
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
