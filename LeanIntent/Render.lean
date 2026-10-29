import Lean
import LeanIntent.Explain
import LeanIntent.Print
import LeanIntent.Print.Meaning
import LeanIntent.Cone

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
declarations of Lean's own libraries, whose modules Lean found in the library directory of the
release that runs (`leanOwnModules`), and the text records that release and its commit instead;
the definitions of lean-intent itself are printed like a project's. For an intent record, and an
answer to it, it also stops at the record's own constant, whose meaning is shown statement by
statement.

Each declaration collected is printed in full, or the text is refused (`declSection`): a
definition's type and value; a definition by structural or well-founded recursion, which Lean
compiles into a value its syntax cannot write, by its type and the equation Lean proves for it,
`c.eq_def`, which states its value at every argument and determines it; a theorem's, an opaque
constant's and an axiom of a proposition's type, which is all a term that uses one depends on; an
inductive type's type, its number of
parameters and each constructor's type, which for a structure lists its fields; a function that
reads a field of a structure, whose value is checked to be the projection Lean makes, by its type,
the number of `fun`s of its value, its structure and its field's index, which determine its value
up to the names, types and annotations of those `fun`s (`projShape_determines`), while for a
well-typed definition its printed type fixes those types up to definitional equality, which is
argued, not proved. A constructor is printed with its inductive type and a recursor is derived by
Lean's kernel from its inductive types, so neither has a section of its own once those are
printed. An axiom whose type is not a proposition is refused, since in a module of Lean's module
system Lean shows an imported definition whose body is not exposed that way, as is a name with no
declaration and every type, value or equation the printer cannot print or Lean does not read
back. So no text prints a meaning in part.

A definition is shown by its equation exactly when Lean's own record of the definitions it compiled
by structural or by well-founded recursion holds it (`recursionKind`), and its equation is the one
Lean states for it (`Lean.Meta.getUnfoldEqnFor?`), of the form `∀ x₁ … xₙ, c x₁ … xₙ = r`
(`unfoldsTo`), resting with `c` on no axiom but Lean's own (`unfoldEqn`); otherwise it is refused,
naming it. The equation determines the definition: Lean accepts such a definition only when `r`
uses the values of `c`, and of any function defined together with it, only at arguments below
`x₁ … xₙ`, structural subterms or arguments below them by a well-founded relation its termination
proof shows, for `c` or any function in its place, so `r` computes each value from values below
it, and any two functions, or families of functions defined together, that satisfy such equations
are equal (`eq_of_recursion_eqn`, proved for one function of one argument). That Lean's equation has that form is argued
from how Lean compiles these definitions, not proved; that the termination proof is a proof rests
on the axiom check. A definition by `partial_fixpoint`, whose equation need not determine it (for
instance `f n = f (n + 1)`), and every other definition are printed by their value, and refused
when it cannot be printed, such as one that holds a projection. The printer writes a `let` as
`let` and one that does not depend on its value as `have`, as Lean reads them.

Every term is printed by `LeanIntent.Print.print`, whose output `LeanIntent.Print.parse` reads back
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
      throwError "cannot print{indentExpr e}\nthe printer refuses it: it holds a projection, \
        a universe metavariable, or a name it cannot write"
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
def declSection (lookup : Name → Option ConstantInfo) (out : List (Name × ConstantInfo))
    (eqns : NameMap (Name × Expr)) (c : Name) (ci : ConstantInfo) : MetaM (Option String) := do
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
    if let some (eq, t) := eqns.find? c then
      let (kind, shows, below) := if recursionKind (← getEnv) c == some true then
          ("structural recursion", "", "at structural subterms of the arguments it recurses on")
        else ("well-founded recursion", "its termination proof shows that ",
          "at arguments below those on the left by a well-founded relation")
      return some (head s!"A definition by {kind}" ++ s!"Its value is not printed: Lean \
        compiles a definition by recursion into a term its syntax cannot write. In its place is \
        the equation Lean proves for it, `{eq}`, which Lean's kernel checked, stating its value at \
        every argument:\n\n{code (← printPart c "equation" t)}\nThe equation determines {c}: Lean \
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
naming what cannot be printed, when one cannot be, so nothing is printed in part. A definition by
recursion (`recursionKind`) reaches what its type and its equation (`unfoldEqn`) mention, in place
of what its value does: each pass collects the meaning with the equations found so far, following
nothing from a definition by recursion whose equation is not yet found, and then finds those; the
pass that finds none to add is the one printed, so every definition by recursion it reaches is
followed through its equation. Each pass but the last adds the equation of a declaration of the
environment, so there are finitely many. -/
def definitions (roots : List Name) (shown : NameSet) : MetaM String := do
  let own ← leanOwnModules
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
      let mut text := ""
      for (c, ci) in out do
        if let some s ← declSection lookup out found c ci then text := text ++ s
      return text
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
