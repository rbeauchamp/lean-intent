module

public import Lean.CoreM
public import Lean.Class

public section

namespace LeanIntent

open Lean

@[expose] def Loaded (env : Environment) : Prop :=
  isClass env ``Inhabited = true

@[expose] def isLoaded (env : Environment) : Bool :=
  isClass env ``Inhabited

theorem isLoaded_eq_true (env : Environment) : isLoaded env = true ↔ Loaded env :=
  Iff.rfl

@[expose] def notLoaded : String :=
  "the state of Lean's environment extensions is not loaded in this environment (Lean does not \
    record its own class `Inhabited` as a class here), so what this program asks Lean (what a term \
    reduces to under Lean's elaborator, how it prints, whether a declaration is an instance) would \
    be answered from tables left as they start. A program that imports the modules it reads imports \
    them with Lean's `importModules` given `loadExts := true` after `enableInitializersExecution`"

def asking {m : Type → Type} {α : Type} [Monad m] [MonadEnv m] [MonadError m] (x : m α) : m α := do
  unless isLoaded (← getEnv) do
    throwError notLoaded
  x

def askingIn {m : Type → Type} {α : Type} [Monad m] [MonadEnv m] [MonadError m]
    (k : (env : Environment) → Loaded env → m α) : m α := do
  let env ← getEnv
  if h : isLoaded env = true then k env ((isLoaded_eq_true env).mp h) else throwError notLoaded

theorem asking_eq {m : Type → Type} {α : Type} [Monad m] [MonadEnv m] [MonadError m] (x : m α) :
    asking x = (do
      unless isLoaded (← getEnv) do
        throwError notLoaded
      x) := by
  rfl

theorem askingIn_eq {m : Type → Type} {α : Type} [Monad m] [MonadEnv m] [MonadError m]
    (k : (env : Environment) → Loaded env → m α) :
    askingIn k = (do
      let env ← getEnv
      if h : isLoaded env = true then k env ((isLoaded_eq_true env).mp h)
      else throwError notLoaded) := by
  rfl

end LeanIntent
