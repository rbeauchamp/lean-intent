module

public import Lean
public import LeanIntent.Implementation
public import LeanIntent.Confirmation.Read
public import LeanIntent.Loaded

public section

namespace LeanIntent.Implementation.Read

open Lean Meta LeanIntent.Render LeanIntent.Confirmation.Read

def moduleOf (c : Name) : MetaM Name := asking do
  let env ← getEnv
  match env.getModuleIdxFor? c with
  | some idx =>
    match Confirmation.Read.moduleName? env.header idx.toNat with
    | some m => return m
    | none => throwError "the environment records no module of index {idx.toNat}, which declares {c}"
  | none =>
    unless env.contains c do throwError "unknown constant {c}"
    return env.mainModule

@[expose] def constOf? (e : Expr) : Option Name :=
  match e.consumeMData with
  | .const c _ => some c
  | _ => none

def entryOf (decl : Name) : MetaM Entry := asking do
  let t ← readWhnf (← getConstInfo decl).type
  let .app (.app (.const ``Implementation _) _) d := t
    | throwError "the type of {decl} is not `LeanIntent.Implementation` applied to a deliverable"
  let args ← ctorArgs (← Confirmation.Read.constOf decl) ``Implementation.mk 4
  let subject ← match constOf? args[2] with
    | some c => pure (some ⟨← moduleOf c, c⟩)
    | none => pure none
  return ⟨decl, constOf? d, subject⟩

def awaitingEntryOf (decl : Name) : MetaM AwaitingEntry := asking do
  let t ← readWhnf (← getConstInfo decl).type
  let .app (.app (.const ``AwaitingImplementation _) _) d := t
    | throwError
        "the type of {decl} is not `LeanIntent.AwaitingImplementation` applied to a deliverable"
  let args ← ctorArgs (← Confirmation.Read.constOf decl) ``AwaitingImplementation.mk 4
  let reason ← try strLit args[2] catch e =>
    throwError "the reason {decl} gives is not read as a string literal: {e.toMessageData}"
  return ⟨decl, constOf? d, reason⟩

def check (mods : Array Name) : MetaM Report := asking do
  let ds ← declaredIn mods ``Deliverable
  let vs ← (← declaredIn mods ``Implementation).mapM entryOf
  let as ← (← declaredIn mods ``AwaitingImplementation).mapM awaitingEntryOf
  return report ds.toList vs.toList as.toList

end LeanIntent.Implementation.Read
