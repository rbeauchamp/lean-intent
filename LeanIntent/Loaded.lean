module

public import Lean.CoreM
public import Lean.Class

/-!
# Refusing an environment whose extensions' state is not loaded

A program of the library that reads a build is handed its environment by whoever runs it: Lean's
elaboration of a file, or a program that imported the build's modules itself. Lean's elaboration
loads the state of the environment extensions, the tables Lean's own functions consult (which
declarations are classes, which are reducible, what a notation prints as). A program's own import
loads it only when it asks: Lean's `importModules` leaves every extension's state as it starts
unless given `loadExts := true`, and reports nothing (`Lean/Environment.lean` 2428-2432 and 2440,
read at Lean v4.35.0, as is every line this comment cites; `LeanIntent/Imported.lean` says what
loading does). A reader run on such an environment would answer from empty tables, with no error:
no declaration an instance, no notation in a text.

So every program of the library that is handed an environment begins with `asking`, which throws
(`notLoaded`) unless the environment is `Loaded`, and every function that takes an environment as
an argument and asks an extension's state takes a proof of `Loaded` with it. `tools/check.lean`'s
rule `READERS` checks this of every declaration of the library whose type holds an environment,
and names the few it excepts; each of those asks only the constants and the modules' headers, as
the comment of the module that declares it shows from Lean's source.

## What `Loaded` decides

`Loaded env` holds when Lean records its own class `Inhabited` as a class in `env`. `isClass`
reads the map held in the state of the class extension (`Lean/Class.lean` 70-78). That state starts
as the empty map and is loaded as the map of the classes of every imported module
(`Lean/EnvExtension.lean` 47-48, with the extension's `addImportedFn`, `Class.lean` 73).
`Inhabited` is a class of `Init.Prelude` (line 823), which every module but those of Lean's own
prelude imports. So:

* in an environment imported with the extensions' state unloaded, the class extension holds no
  class of an imported module, `Inhabited` is not recorded, and `asking` throws. This is the case
  the test exists for, and it does not pass there;
* in an environment imported with that state loaded, at any level of Lean's module system, the
  class extension holds `Inhabited`: the extension stores a module's classes the same at every
  level, giving no export of its own (`Class.lean` 70-74, `EnvExtension.lean` 51-53), and builds
  its state from the entries of every imported module (`EnvExtension.lean` 20-21). So `asking`
  runs its program there, and the test refuses no environment Lean's elaboration supplies.

The test reads one extension. That the others are loaded where it is rests on Lean loading the
state of every registered persistent extension or of none: one branch on `loadExts` runs
`finalizePersistentExtensions` over all of them (`Environment.lean` 2404-2405 and 1976-2007).
That, and that nothing but an import recorded `Inhabited` as a class, is trusted. The tables claim
nothing of a toolchain other than the one cited.
-/

public section

namespace LeanIntent

open Lean

/-- `Loaded env`: the state of Lean's environment extensions is loaded in `env`, as far as a
program can tell: Lean records its own class `Inhabited` as a class there (`isClass`, which reads
the state of the class extension). The module comment says why this decides it. -/
@[expose] def Loaded (env : Environment) : Prop :=
  isClass env ``Inhabited = true

/-- Decides `Loaded`. -/
@[expose] def isLoaded (env : Environment) : Bool :=
  isClass env ``Inhabited

theorem isLoaded_eq_true (env : Environment) : isLoaded env = true ↔ Loaded env :=
  Iff.rfl

/-- What a program of the library reports where the state of the environment's extensions is not
loaded. -/
@[expose] def notLoaded : String :=
  "the state of Lean's environment extensions is not loaded in this environment (Lean does not \
    record its own class `Inhabited` as a class here), so what this program asks Lean (what a term \
    reduces to under Lean's elaborator, how it prints, whether a declaration is an instance) would \
    be answered from tables left as they start. A program that imports the modules it reads imports \
    them with `LeanIntent.Imported.loaded`, or with Lean's `importModules` given `loadExts := true` \
    after `enableInitializersExecution`"

/-- **`x`, run only where the state of the environment's extensions is loaded** (`Loaded`): in any
other environment, an error (`notLoaded`) thrown before `x` asks anything. Every program of the
library that is handed an environment by its caller begins with it, which `tools/check.lean`'s rule
`READERS` checks. -/
def asking {m : Type → Type} {α : Type} [Monad m] [MonadEnv m] [MonadError m] (x : m α) : m α := do
  unless isLoaded (← getEnv) do
    throwError notLoaded
  x

/-- **`k`, run only where the state of the environment's extensions is loaded**, on the current
environment with the proof that it is, for a program that calls a function requiring that proof. -/
def askingIn {m : Type → Type} {α : Type} [Monad m] [MonadEnv m] [MonadError m]
    (k : (env : Environment) → Loaded env → m α) : m α := do
  let env ← getEnv
  if h : isLoaded env = true then k env ((isLoaded_eq_true env).mp h) else throwError notLoaded

/-- **`asking` asks nothing of an environment that is not loaded.** Its first act is the decision
`isLoaded` on the current environment, and `x` runs only where that holds. This specifies the
request; that Lean's monads run it in this order is trusted with Lean. -/
theorem asking_eq {m : Type → Type} {α : Type} [Monad m] [MonadEnv m] [MonadError m] (x : m α) :
    asking x = (do
      unless isLoaded (← getEnv) do
        throwError notLoaded
      x) := by
  rfl

/-- **`askingIn` asks nothing of an environment that is not loaded**, and gives `k` the current
environment with the proof only where the decision `isLoaded` holds. -/
theorem askingIn_eq {m : Type → Type} {α : Type} [Monad m] [MonadEnv m] [MonadError m]
    (k : (env : Environment) → Loaded env → m α) :
    askingIn k = (do
      let env ← getEnv
      if h : isLoaded env = true then k env ((isLoaded_eq_true env).mp h)
      else throwError notLoaded) := by
  rfl

end LeanIntent
