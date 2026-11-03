import Lean
import LeanIntent.Implementation
import LeanIntent.Confirmation.Read

/-!
# Reading a project's implementations from the finished build

`LeanIntent.Implementation` decides whether each deliverable of a project names its implementation,
given what the build shows of its deliverables and of its values of `Implementation d`. This module
reads both from Lean's environment, so a gate that reads only the declarations of a finished build
reads them through the library, and parses no source text. Each input is read through Lean:

| Input | How it is read |
|---|---|
| the project's deliverables | as `LeanIntent.Confirmation.Read.check` reads them: every definition, opaque constant or axiom of the modules given whose type reduces, unfolding every definition, to `LeanIntent.Deliverable _` |
| the values that record implementations | every such constant of those modules whose type so reduces to `LeanIntent.Implementation _` |
| the deliverable a value names | the second argument of that type, `d` of `@Implementation W d`, where it is a constant once its metadata is removed (`Expr.consumeMData`), and otherwise none |
| the constant a value records | its value, reduced by `whnf` with every definition unfolded to `Implementation.mk`'s application, and that application's third argument, the subject, where it is a constant once its metadata is removed, and otherwise none; `whnf` reduces the head of a term and no argument, so the subject is read as the value holds it, never unfolded |
| that constant's module | the module the environment records as declaring it (`Environment.getModuleIdxFor?`), or the module being elaborated when it is declared there |

A value whose value does not reduce to the constructor's application, such as an opaque constant or
an axiom, is an error naming it, never a pass: Lean's `whnf` unfolds only definitions
(`Meta.getUnfoldableConst?`). So is an unsafe value, as `declaredIn` refuses every unsafe constant it
finds: an unsafe definition may refer to itself, so its proof could prove anything, while a safe one
cannot refer to an unsafe constant, which Lean's kernel refuses. What a value's proof proves is fixed
by its type and was checked by Lean's kernel when the value was declared, so nothing here reads a
theorem's statement.

The modules given are the caller's, and should be every module of the project, as Lake lists them,
the same list given to `LeanIntent.Confirmation.Read.check`: a module left out hides what it
declares, so a value in it records nothing and its deliverable is refused as unimplemented, and a
deliverable in it is not asked about. A constant whose type is not one of these once unfolded, such
as a function returning a value of `Implementation d` or a structure holding one, is not found, so
it records nothing.
-/

namespace LeanIntent.Implementation.Read

open Lean Meta LeanIntent.Render LeanIntent.Confirmation.Read

/-- The module that declares the constant `c`, as the environment records it: the imported module
that holds it, or the module being elaborated when it is declared there. -/
def moduleOf (c : Name) : MetaM Name := do
  let env ← getEnv
  match env.getModuleIdxFor? c with
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some m => return m
    | none => throwError "the environment records no module of index {idx.toNat}, which declares {c}"
  | none =>
    unless env.contains c do throwError "unknown constant {c}"
    return env.mainModule

/-- The constant `e` is, once its metadata is removed, or none. -/
def constOf? (e : Expr) : Option Name :=
  match e.consumeMData with
  | .const c _ => some c
  | _ => none

/-- What the build shows of the value `decl`, a constant whose type reduces to `Implementation d`:
the deliverable its type names and the constant its subject is, each where it is a constant. An
error when its value does not reduce to `Implementation.mk`'s application. -/
def entryOf (decl : Name) : MetaM Entry := do
  let t ← withTransparency .all (whnf (← getConstInfo decl).type)
  unless t.isAppOfArity ``Implementation 2 do
    throwError "the type of {decl} is not `LeanIntent.Implementation` applied to a deliverable"
  let args ← withTransparency .all (ctorArgs (← Confirmation.Read.constOf decl) ``Implementation.mk 4)
  let subject ← match constOf? args[2]! with
    | some c => pure (some ⟨← moduleOf c, c⟩)
    | none => pure none
  return ⟨decl, constOf? t.appArg!, subject⟩

/-- **What a gate reads**, from the finished build: the report on the implementations of the project
whose modules are `mods`. It is `Implementation.report` of the project's deliverables and the entries
of its values of `Implementation d`, so its findings are empty exactly when each deliverable has
exactly one value recording its implementation, each value names one of them and records a constant,
and there is at least one deliverable (`Implementation.findings_eq_nil_iff`). -/
def check (mods : Array Name) : MetaM Report := do
  let ds ← declaredIn mods ``Deliverable
  let vs ← (← declaredIn mods ``Implementation).mapM entryOf
  return report ds.toList vs.toList

end LeanIntent.Implementation.Read
