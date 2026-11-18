module

public import Lean

/-!
# Importing a finished build's modules into a program

A program that reads a finished build, rather than running while Lean elaborates a file, imports the
build's modules itself, with Lean's `importModules`. That call builds the constants, each module's
header and the entries each module stored for each environment extension in every case. It builds
the *state* of the extensions, the tables Lean's own functions consult (which declarations are
classes, which are reducible, what a notation prints as), only when it is given `loadExts := true`.
The default is `false`, and then, as its documentation says, every extension has its initial value
as its state, and many functions that take an `Environment`, or are in a monad carrying one such as
`CoreM`, may not function properly (`Lean/Environment.lean` 2428-2432 and 2440, read at Lean
v4.35.0, as is every line this comment cites). Nothing reports it: `isClass` (`Lean/Class.lean`
77-78) answers no for every declaration, from an empty table.

This module holds the library's two ways to import, one for each kind of reader.
`tools/check.lean`'s rule `LOADED` refuses a declaration, of the library or of a file under
`tools/`, that imports in any other way.

## `loaded`: every extension's state, as Lean's frontend imports

`loaded mods` imports as Lean's frontend imports the modules a file names (`Lean/Elab/Import.lean`
159): with `loadExts := true`, after `enableInitializersExecution`. `finalizeImport` then runs
`finalizePersistentExtensions` (`Environment.lean` 2404-2405 and 1976-2007), which takes every
persistent extension registered in the process, in turn, and sets its state to what its
`addImportedFn` builds from the entries the modules stored for it (1989-1990). At the extension of
the `init` attribute it then runs the `initialize` declarations of the imported modules
(1991-1995), which is what registers an extension or an attribute that one of those modules
declares, so that its state is built in a later turn (1996-2003). Lean refuses to run them, and
with them the import, unless `enableInitializersExecution` was called since the process last
imported (`Lean/Compiler/InitAttr.lean` 199-201; `withImporting` unsets the flag when an import
ends, `Lean/ImportingFlag.lean` 54-60), so `loaded` calls it each time.

The level is `importModules`'s default, `private`: all data is loaded as if no imported module were
a `module` file (`Environment.lean` 2434-2437), so the declarations and the bodies that a `module`
file keeps private are read as well.

A reader of a `loaded` environment may ask Lean what a metaprogram asks while Lean elaborates a file
that imports the same modules in full, and gets the answer it would get there. Two kinds of
extension do not hold what "loaded" suggests, there or here, and a reader that relies on one says
so:

* an extension whose `addImportedFn` builds nothing from the entries, such as the one that stores
  compiled code (`declMapExt`, `Lean/Compiler/IR/CompilerM.lean` 83-85): its state holds only what
  the current module adds, and what the modules stored is found through their entries
  (`getModuleEntries`, `getModuleIREntries`), as `IR.findEnvDecl` finds it;
* an extension that is not persistent (`registerEnvExtension`, `Environment.lean` 1517-1527), whose
  state no module stores: it has its initial state after any import.

**What running the initializers admits.** The `initialize` declarations of every module imported run
in the program's process, as they do in every `lean` process that imports those modules; those the
interpreter runs, at most once for a module in a process (`InitAttr.lean` 176-180). They are code of
the modules being read: one can register what it likes, print, or end the process with a status of
its choosing. So a program that imports with `loaded` trusts the code of the modules it reads as a
build that imports them does, and its verdict on modules written to defeat it means nothing. Lean's
conditions on `enableInitializersExecution` (`ImportingFlag.lean` 19-28) are the program's to keep:
no other thread runs while it imports; the native code the process has loaded for a module is that
of the module imported, which holds where the process imports one build of each module; and the
imported regions are never freed, which nothing here does. `loaded` is `unsafe` because
`enableInitializersExecution` is.

## `stored`: what the modules stored, and no extension's state

`stored root opts` imports the module `root` and what it imports with `importModules` as it is by
default, `loadExts := false`, which runs no code of the modules, and it hands back no environment.
A `Stored` holds four questions and nothing else, each answered from what `finalizeImport` builds
whatever `loadExts` is:

| Question | What answers it | Where `finalizeImport` builds it |
|---|---|---|
| `contains n` | the constant map (`Environment.contains`, `Environment.lean` 1146-1147) | 2333-2345 and 2363-2365 |
| `moduleOf n` | the module recorded for each constant, and for each stored IR declaration the modules hold no constant of (`Environment.getModuleIdxFor?`, 1196-1198), with the modules' names | 2345-2348, and the header, 2369-2373 |
| `modules` | each module's name with the modules it imports, as its file records them (`ModuleData.imports`) | the header, 2369-2373 |
| `irDecl? n` | `IR.findEnvDecl` (`CompilerM.lean` 142-143): the entries the declaration's module stored for the extension of compiled code, its IR entries first (`Lean/Compiler/LCNF/Basic.lean` 1252-1261), and then that extension's state | the entries by `setImportedEntries`, 2377 and 2382, before `loadExts` is read at 2404; the state is the empty map with `loadExts` off and on alike, since it starts as what the extension's `addImportedFn` builds from no entries and is loaded as what that builds from the modules' (`Lean/EnvExtension.lean` 47-48), and that function builds the empty map from any entries (`CompilerM.lean` 83-85) |

So no question of a `Stored` is answered from a state that loading would change. The environment
does not leave `stored`: these four functions are all that a reader given a `Stored` has of it, so
the reader has nothing to hand to a function that reads an extension's state. A reader that needs
another question adds it here, with its row.
-/

public section

namespace LeanIntent.Imported

open Lean

/-- **The environment of the modules `mods` and what they import, with every environment
extension's state loaded**, as Lean's frontend imports a file's modules: `importModules` with
`loadExts := true`, at its default level `private`, after `enableInitializersExecution`, which Lean
requires and which lets the import run the `initialize` declarations of the imported modules in
this process. The module comment says what that admits and what Lean asks of the program. An error
when Lean cannot import a module. -/
unsafe def loaded (mods : Array Name) : IO Environment := do
  enableInitializersExecution
  importModules (mods.map fun m => { module := m }) {} (loadExts := true)

/-- **What an import stored**, as four questions that no environment extension's state answers. It
holds no environment, so a reader given one can ask Lean nothing else of the import. The module
comment's table says what each question reads. -/
structure Stored where
  /-- Whether the modules hold a constant named `n`. -/
  contains : Name → Bool
  /-- The module that `n` belongs to: the one that declares the constant `n`, or, for a declaration
  the modules hold no constant of, the one whose stored IR holds it. -/
  moduleOf : Name → Option Name
  /-- Each module imported, with the modules it imports. -/
  modules : Array (Name × Array Name)
  /-- The IR the build stored for the declaration `n`, as Lean finds it (`IR.findEnvDecl`). -/
  irDecl? : Name → Option IR.Decl

/-- **What the build stored of the module `root` and what it imports**: Lean's `importModules` of
`root` alone, with no extension's state loaded and no code of the modules run, read into a `Stored`.
The environment is kept only inside the four functions. An error when Lean cannot import `root`. -/
def stored (root : Name) (opts : Options) : IO Stored := do
  let env ← importModules #[{ module := root }] opts
  return {
    contains := fun n => env.contains n
    moduleOf := fun n => (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?
    modules := env.header.moduleNames.mapIdx fun i m =>
      (m, ((env.header.moduleData[i]?.map (·.imports)).getD #[]).map (·.module))
    irDecl? := fun n => IR.findEnvDecl env n }

end LeanIntent.Imported
