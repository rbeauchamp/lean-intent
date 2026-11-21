module

public import Lean
public import LeanIntent.Required
public import LeanIntent.Required.ModuleName
public import LeanIntent.Implementation.Read

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
| the modules whose declarations are read | every module the environment holds, the one being elaborated included: `check` takes no list of modules to read, so none can be left out of what it reads; each module's declarations are read from that module's own data, as Lean loaded it (`EnvironmentHeader.moduleData`), and the file's own from the constants it added, never from the environment's one map of constants |
| the project's deliverables | every definition, opaque constant or axiom of those modules whose type reduces through Lean's kernel (`Render.readWhnf`), unfolding every definition, to `LeanIntent.Deliverable _` |
| the values that record implementations | every such constant whose type so reduces to `LeanIntent.Implementation _` |
| the values that name required theorems | every such constant whose type so reduces to `LeanIntent.Required _` |
| the deliverable such a value names | the second argument of that type, `d` of `@Required W d`, where it is a constant once its metadata is removed (`Expr.consumeMData`), and otherwise none |
| what such a value lists | its value, reduced by `Render.readWhnf` through the kernel to `Required.mk`'s application, that application's third argument reduced to a list (`Render.listElems`), and each element reduced to `Proof.mk`'s application, whose second argument, the proof, is read as the value holds it: a constant once its metadata is removed, and otherwise a term; where Lean's elaborator abstracted a proof term into an auxiliary theorem of the value's own module, the value holds that theorem's constant, which is read as that theorem |
| whether a listed constant is a theorem | the declaration of its name in the data of the module the environment records for it (`ownDeclaration`), a theorem exactly when that declaration is `ConstantInfo.thmInfo` with the type and universe parameters of the declaration the environment holds, which the value's entry was checked against; the environment's map of constants does not decide it, since Lean puts a later module's theorem there over an earlier module's axiom of the same type (`subsumesInfo` and `finalizeImport` in Lean v4.35.0's `src/Lean/Environment.lean`, lines 2269 to 2284 and 2333 to 2345) |
| the module that declares a constant | for a deliverable, a value recording an implementation or a value of `Required`, the module in whose own data it was found, with an error where the environment holds another declaration under its name (`sameDeclaration`); for a listed constant, the module the environment records for the name (`Environment.getModuleIdxFor?`), the first in import order to declare it, provided that module's own data declares the name, and otherwise an error naming both, as where the module holds the name only as an auxiliary name of its compiled code (`const2ModIdx.insertIfNew`, lines 2345 and 2348 of the same file); a constant with no module index is declared in the file being elaborated |
| the module names the build lists | given by the caller; `queryModules` reads them from what `lake query --json` prints for `@/<library>:modules`, each line a JSON array of names, read by Lean's JSON parser, and each name decoded by `Required.moduleName?`, which gives a name only for a string of its closed form and for which distinct strings give distinct names (`Required.moduleName?_inj`); every other string is an error naming it |

**Every module is read in full, or the check refuses to run.** `check` is an error in a `module`
file. Where the file being elaborated is not one, Lean imports every module its imports reach, with
everything each declares, whatever those modules' own imports say of visibility
(`importModulesCore` in Lean v4.35.0's `src/Lean/Environment.lean`, lines 2121 to 2123 and 2183,
with the level `Elab.processHeaderCore` gives it, `src/Lean/Elab/Import.lean`, lines 150 to 159).
Where it is a `module` file, Lean imports only what each module exports: a private value is absent,
a theorem is shown as an axiom, and a module reached only through a private import is not loaded at
all (lines 2125 to 2175, 2249 to 2252). A value of `Required` could then go unread, so the check
does not run there (`Environment.header`'s `isModule`, which `finalizeImport` sets at line 2370).

**Every module the build lists must be imported**, or `check` is an error naming the first that is
not: a deliverable in a module that is not imported would not be asked about.

A value of `Required` whose value does not reduce to its constructor's application, such as an
opaque constant or an axiom, is an error naming it, never a pass, and so is every unsafe or partial
constant of the types read here: `declaredAnywhere` requires every definition it finds to have
safety `safe` (`Confirmation.Read.proofSafe_iff`). A theorem Lean records is safe, and a safe
declaration cannot refer to an unsafe or partial one, which Lean's kernel refuses.

## Why the name `queryModules` gives is the name Lake printed

Argued from Lean's source at v4.35.0, not proved here. Lake prints a module's name as Lean's
`ToJson Name` writes it, the string `Name.toString` gives with its defaults
(`src/Lean/Data/Json/FromToJson/Basic.lean`, lines 186 to 187; `src/Init/Data/ToString/Name.lean`,
lines 123 to 127). Take a name `n` that Lean prints as a string `s` that `Required.moduleName?`
accepts, so that `s` holds only dots, ASCII letters and digits, `_` and `'`
(`Required.moduleName?_chars`) and each stretch between its dots starts with a letter
(`Required.moduleName?_isPart`). Then:

* `n` is not the anonymous name, printed `[anonymous]`, and has no numeric component, which is
  printed as its digits and would start a stretch with a digit (`toStringWithSep`, lines 73 to 83).
* Escaping is on for `n`. It is off only for a name whose last string component holds `✝` or is
  `_inaccessible` (`Name.isInaccessibleUserName`, `src/Init/Meta/Defs.lean`, lines 152 to 155), a
  name with macro scopes, whose last string component is `_hyg` (`Name.hasMacroScopes`,
  `src/Init/Prelude.lean`), the name `_`, and a name whose first component starts with `#` or `?`
  (`toStringWithToken`, lines 100 to 112). Each component is then printed as it stands, so `s`
  would hold `✝`, or a stretch `_inaccessible`, `_hyg` or `_`, or would start with `#` or `?`.
* With escaping on, a string component is printed as it stands only where it is an identifier, a
  first character that `isIdFirst` accepts followed by characters that `isIdRest` accepts, none of
  which is a dot (`src/Init/Meta/Defs.lean`, lines 120 to 121 and 133 to 134), or where it holds
  `»`; every other component is printed between `«` and `»` (`escapePart`, lines 55 to 64). `s`
  holds neither `«` nor `»`, so every component of `n` is an identifier with no dot, printed as it
  stands.

So `s` is `n`'s components with a dot between each two, none holding a dot: the stretches of `s`
are exactly `n`'s components, and `Required.nameOf` of them is `n`. A name Lean prints otherwise,
such as one with a component that holds a dot, a non-ASCII letter, `!` or `?`, or that starts with
`_`, is refused by name, never read as another.

The module names given as the build's are trusted to be those Lake builds for the project's proof
check; `docs/required-theorems.md` says how to read them from Lake.
-/

public section

namespace LeanIntent.Required.Read

open Lean Meta LeanIntent.Render LeanIntent.Confirmation.Read LeanIntent.Implementation.Read

/-- Whether `held`, the declaration the environment holds of a name, is `own`, a declaration of
that name read from one module's own data, as far as this reader reads a declaration: the same kind
of constant, with the same universe parameters and type, and for a definition the same value.
Stated for the kinds `declaredAnywhere` finds, a definition, an opaque constant and an axiom; of
every other kind it is false. -/
@[expose] def sameDeclaration (own held : ConstantInfo) : Bool :=
  own.levelParams == held.levelParams && own.type == held.type &&
    match own, held with
    | .defnInfo a, .defnInfo b => a.value == b.value
    | .opaqueInfo _, .opaqueInfo _ | .axiomInfo _, .axiomInfo _ => true
    | _, _ => false

/-- **The module that declares the constant `c`, with that module's own declaration of it.** The
module is the one the environment records for the name (`Environment.getModuleIdxFor?`), and the
declaration is read from the data Lean loaded for that module (`EnvironmentHeader.moduleData`), not
from the environment's map of constants, in which a declaration of another module may stand under
the name. A name the environment records under no module is declared in the file being elaborated,
and is read from the constants that file added (`constants.map₂`). An error naming the constant and
the module where the module recorded does not itself declare the name, as when the name is only an
auxiliary name of that module's compiled code. -/
def ownDeclaration (c : Name) : MetaM (Name × ConstantInfo) := do
  let env ← getEnv
  match env.getModuleIdxFor? c with
  | some idx =>
    let some m := Confirmation.Read.moduleName? env.header idx.toNat
      | throwError "the environment records no module of index {idx.toNat}, which declares {c}"
    match env.header.moduleData[idx.toNat]?.bind (·.constants.find? (·.name == c)) with
    | some own => return (m, own)
    | none =>
      throwError "the environment records {c} under the module {m}, which does not itself declare \
        it, so the module that declares it cannot be read"
  | none =>
    match env.constants.map₂.find? c with
    | some own => return (env.mainModule, own)
    | none =>
      throwError "the environment records {c} under no module, and the file being elaborated \
        does not declare it, so the module that declares it cannot be read"

/-- What the build shows of one element `e` of a `Required` value's list, a term of type
`LeanIntent.Proof`: the theorem its proof is, the other constant it is, or a term. A constant is
read by `ownDeclaration`: it is a theorem exactly when the module the environment records for it
itself declares it as a theorem, with the type and universe parameters of the declaration the
environment holds, which is the one the value's entry was checked against; where that module
declares it as anything else, such as an axiom that a module imported later proves, it is another
constant. An error where that module's theorem differs in type or universe parameters. -/
def citedOf (e : Expr) : MetaM Cited := do
  let args ← ctorArgs e ``Proof.mk 2
  match constOf? args[1]! with
  | none => return .term
  | some c =>
    let (m, own) ← ownDeclaration c
    match own with
    | .thmInfo _ =>
      let held ← getConstInfo c
      unless own.levelParams == held.levelParams && own.type == held.type do
        throwError "the module {m} declares the theorem {c} with another statement than the \
          environment holds for that name, so it is not read"
      return .thm ⟨m, c⟩
    | _ => return .other ⟨m, c⟩

/-- What the build shows of the value `decl`, a constant whose type reduces to `Required d`, as
`declaredAnywhere` found it, with the module whose own data declares it: that module, the
deliverable its type names, where that is a constant, and what it lists. An error when its value
does not reduce to `Required.mk`'s application, or its list to a list. -/
def entryOf (decl : Implementation.Constant) : MetaM Entry := do
  let t ← readWhnf (← getConstInfo decl.name).type
  unless t.isAppOfArity ``Required 2 do
    throwError "the type of {decl.name} is not `LeanIntent.Required` applied to a deliverable"
  let args ← ctorArgs (← Confirmation.Read.constOf decl.name) ``Required.mk 4
  let theorems ← (← listElems args[2]!).mapM citedOf
  return ⟨decl.name, decl.module, constOf? t.appArg!, theorems.toList⟩

/-- The definitions, opaque constants and axioms of every module the environment holds, the one
being elaborated included, whose type, reduced through the kernel by unfolding every definition, is
an application of one of the constants `heads`, each by the module that declares it and its name,
with that constant, sorted by name. Each module's declarations are read from that module's own
data, as Lean loaded it (`EnvironmentHeader.moduleData`, at the index of the module's name), and
those of the file being elaborated from the constants it added (`constants.map₂`), so the module
given for a constant is one whose own data declares it, and no module is left out. A constant found
is one the environment holds as that module declares it (`sameDeclaration`), or an error naming
both, since its type and value are then read through the environment. An opaque constant or an
axiom is found so that reading it is an error, never a value passed over, and a constant found that
is unsafe or partial is an error (`Confirmation.Read.proofSafe_iff`), as
`Confirmation.Read.declaredWhere` makes it for the modules it is given. -/
def declaredAnywhere (heads : Array Name) : MetaM (Array (Implementation.Constant × Name)) := do
  let env ← getEnv
  let read (ci : ConstantInfo) := ci matches .defnInfo _ | .opaqueInfo _ | .axiomInfo _
  let mut candidates : Array (Name × ConstantInfo) := #[]
  for h : i in [0:env.header.moduleData.size] do
    let some m := Confirmation.Read.moduleName? env.header i
      | throwError "the environment names no module of index {i}, whose declarations it holds"
    for ci in env.header.moduleData[i].constants do
      if read ci then candidates := candidates.push (m, ci)
  candidates := env.constants.map₂.foldl (init := candidates) fun acc _ ci =>
    if read ci then acc.push (env.mainModule, ci) else acc
  let mut found : Array (Implementation.Constant × Name) := #[]
  for (m, ci) in candidates do
    if let .const head _ := (← readWhnf ci.type).getAppFn then
      if heads.contains head then
        unless proofSafe ci do
          throwError "{ci.name} is unsafe or partial, so its proofs could prove anything, and it is \
            not read"
        unless (env.find? ci.name).any (sameDeclaration ci) do
          throwError "the module {m} declares {ci.name}, and the environment holds another \
            declaration of that name, so it is not read"
        found := found.push (⟨m, ci.name⟩, head)
  return found.qsort fun a b => Name.lt a.1.name b.1.name

def check (built : Array Name) : MetaM Report := do
  let env ← getEnv
  if env.header.isModule then
    throwError "the required-theorems check reads every declaration of every module imported, and \
      a `module` file imports only what each module exports, so a value could go unread: run the \
      check from a file that is not a `module` file"
  for m in built do
    unless m == env.mainModule || (env.getModuleIdx? m).isSome do
      throwError "the module {m}, which the build lists, is not imported here, so what it declares \
        cannot be read"
  let found ← declaredAnywhere #[``Deliverable, ``Implementation, ``Required]
  let of (head : Name) := found.filterMap fun (c, h) => if h == head then some c else none
  let rs ← (of ``Required).mapM entryOf
  return report built.toList (of ``Deliverable).toList (of ``Implementation).toList rs.toList

/-- **The module names a build lists**, read from `out`, what `lake query --json` prints for one or
more targets `@/<library>:modules`: one line for each target, each a JSON array of the names of the
modules that library's `leanArts` facet builds, as Lake encodes a name (`ToJson Name`). Each name is
decoded by `Required.moduleName?`, which gives a name only for a string of its closed form, dots
between stretches that are each an ASCII letter followed by ASCII letters, digits, `_` or `'`, and
gives distinct names for distinct strings (`Required.moduleName?_inj`). Every other string, such as
one that holds `«`, is an error naming it, never a name. Blank lines are passed over; anything else,
and output that lists no module at all, is an error. -/
@[expose] def queryModules (out : String) : Except String (Array Name) := do
  let mut mods : Array Name := #[]
  for line in out.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    let json ← Json.parse line
    let .arr items := json
      | throw s!"a line of Lake's output is not a JSON array of module names: {line}"
    for item in items do
      let .str s := item
        | throw s!"an entry of Lake's output is not a module name: {item.compress}"
      match moduleName? s with
      | some n => mods := mods.push n
      | none =>
        throw s!"the module name {s} is not of the form this check reads, which is dots between \
          parts that are each an ASCII letter followed by ASCII letters, digits, `_` or `'`, so it \
          is not read as any module: give the check the build's module names from Lake's own \
          values instead"
  if mods.isEmpty then
    throw "Lake's output lists no module, so no module is known to be built"
  return mods

end LeanIntent.Required.Read
