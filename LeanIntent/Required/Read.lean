import Lean
import LeanIntent.Required
import LeanIntent.Implementation.Read

/-!
# Reading where a project's required theorems lie, from the finished build

`LeanIntent.Required` decides whether every theorem the intent-first procedure requires of a
project, and that the project names, lies in a module its build lists, given the module names the
build lists and what the build shows of the project's deliverables, of its values of
`Implementation d` and of its values of `Required d`. This module reads the declarations from
Lean's environment, and the module names from what Lake prints of its own `modules` facets, so a
gate reads both through the systems that own them and parses no Lean source text. Each input is
read so:

| Input | How it is read |
|---|---|
| the project's deliverables | as `LeanIntent.Confirmation.Read.check` reads them: every definition, opaque constant or axiom of the modules given whose type reduces, unfolding every definition, to `LeanIntent.Deliverable _` |
| the values that record implementations | as `LeanIntent.Implementation.Read.check` reads them: every such constant of those modules whose type so reduces to `LeanIntent.Implementation _` |
| the values that name required theorems | every such constant of those modules whose type so reduces to `LeanIntent.Required _` |
| the deliverable such a value names | the second argument of that type, `d` of `@Required W d`, where it is a constant once its metadata is removed (`Expr.consumeMData`), and otherwise none |
| what such a value lists | its value, reduced by `Render.readWhnf` through the kernel to `Required.mk`'s application, that application's third argument reduced to a list (`Render.listElems`), and each element reduced to `Proof.mk`'s application, whose second argument, the proof, is read as the value holds it: a constant once its metadata is removed, and otherwise a term; where Lean's elaborator abstracted a proof term into an auxiliary theorem of the value's own module, the value holds that theorem's constant, which is read as that theorem |
| whether a listed constant is a theorem | its declaration in the environment (`getConstInfo`), a theorem exactly when it is `ConstantInfo.thmInfo` |
| the module that declares a constant | the module the environment records as declaring it (`Environment.getModuleIdxFor?`), or the module being elaborated when it is declared there (`Implementation.Read.moduleOf`) |
| the module names the build lists | given by the caller; `queryModules` reads them from what `lake query --json` prints for `@/<library>:modules`, each line a JSON array of names, read by Lean's JSON parser and its decoding of a name (`Name.fromJson?`, which reads a name as Lean's name literals write it, `«` and `»` included), and accepted only where Lean's encoding of the name, which is Lake's (`ToJson Name`), gives back the very string |

A value of `Required` whose value does not reduce to its constructor's application, such as an
opaque constant or an axiom, is an error naming it, never a pass, and so is every unsafe or partial
constant of the types read here, since each is found through `Confirmation.Read.declaredIn`, which
requires every definition it finds to have safety `safe` (`Confirmation.Read.proofSafe_iff`). A
theorem Lean records is safe, and a safe declaration cannot refer to an unsafe or partial one, which
Lean's kernel refuses.

The modules given are the caller's, and should be the module names the build lists, the same list
given to `LeanIntent.Confirmation.Read.check` and `LeanIntent.Implementation.Read.check`: a module
left out hides what it declares, so a deliverable in it is not asked about, and one given that the
build does not list is refused wherever it declares a deliverable or a value recording an
implementation. The module names given as the build's are trusted to be those Lake builds for the
project's proof check; `docs/required-theorems.md` says how to read them from Lake.
-/

namespace LeanIntent.Required.Read

open Lean Meta LeanIntent.Render LeanIntent.Confirmation.Read LeanIntent.Implementation.Read

/-- The constant `c`, by the module the environment records as declaring it and its name. -/
def located (c : Name) : MetaM Implementation.Constant :=
  return ⟨← moduleOf c, c⟩

/-- What the build shows of one element `e` of a `Required` value's list, a term of type
`LeanIntent.Proof`: the theorem its proof is, the other constant it is, or a term. -/
def citedOf (e : Expr) : MetaM Cited := do
  let args ← ctorArgs e ``Proof.mk 2
  match constOf? args[1]! with
  | none => return .term
  | some c =>
    let at' ← located c
    match ← getConstInfo c with
    | .thmInfo _ => return .thm at'
    | _ => return .other at'

/-- What the build shows of the value `decl`, a constant whose type reduces to `Required d`: the
deliverable its type names, where that is a constant, and what it lists. An error when its value
does not reduce to `Required.mk`'s application, or its list to a list. -/
def entryOf (decl : Name) : MetaM Entry := do
  let t ← readWhnf (← getConstInfo decl).type
  unless t.isAppOfArity ``Required 2 do
    throwError "the type of {decl} is not `LeanIntent.Required` applied to a deliverable"
  let args ← ctorArgs (← Confirmation.Read.constOf decl) ``Required.mk 4
  let theorems ← (← listElems args[2]!).mapM citedOf
  return ⟨decl, constOf? t.appArg!, theorems.toList⟩

/-- **What a gate reads**, from the finished build: the report on where the required theorems of
the project whose modules are `mods` lie, given `built`, the module names its build lists. It is
`Required.report` of those names, the project's deliverables and values recording implementations,
each by the module that declares it, and the entries of its values of `Required`, so its findings
are empty exactly when the project declares no value of `Required`, or each deliverable and each
value recording an implementation is declared in a module `built` names, each deliverable is named by a value of `Required`, each such value names a
deliverable, and each thing such a value lists is a theorem declared in a module `built` names
(`Required.findings_eq_nil_iff`, of the entries as this module reads them). -/
def check (mods built : Array Name) : MetaM Report := do
  let ds ← (← declaredIn mods ``Deliverable).mapM located
  let vs ← (← declaredIn mods ``Implementation).mapM located
  let rs ← (← declaredIn mods ``Required).mapM entryOf
  return report built.toList ds.toList vs.toList rs.toList

/-- **The module names a build lists**, read from `out`, what `lake query --json` prints for one or
more targets `@/<library>:modules`: one line for each target, each a JSON array of the names of the
modules that library's `leanArts` facet builds, as Lake encodes a name (`ToJson Name`). Each name is
decoded by Lean's own decoding (`Name.fromJson?`, which reads a name as Lean's name literals write
it) and accepted only where encoding it again gives back the very string, so a name whose string
Lean does not read back as itself, such as one Lean writes without the `«` and `»` its components
need, is an error naming it, never a different name. Blank lines are passed over; anything else, and
output that lists no module at all, is an error. -/
def queryModules (out : String) : Except String (Array Name) := do
  let mut mods : Array Name := #[]
  for line in out.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    let json ← Json.parse line
    let .arr items := json
      | throw s!"a line of Lake's output is not a JSON array of module names: {line}"
    for item in items do
      let .str s := item
        | throw s!"an entry of Lake's output is not a module name: {item.compress}"
      let n ← Name.fromJson? item
      unless (toJson n).compress == item.compress do
        throw s!"the module name {s} is not read back as the same name, so it is not read"
      mods := mods.push n
  if mods.isEmpty then
    throw "Lake's output lists no module, so no module is known to be built"
  return mods

end LeanIntent.Required.Read
