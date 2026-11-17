# The executable that runs a deliverable

**The executable that runs a deliverable** (`LeanIntent.Runs`, `LeanIntent.Execution`, `LeanIntent.Execution.Read`, `LeanIntent.Execution.lakeExecutables`): a value a project declares for each executable target meant to run a deliverable, naming the target as its Lake configuration does; the check, read from the finished build, that each such executable's entry point, the `main` of its root module and what it imports, reaches the deliverable's recorded implementation through the code the build compiled, refusing a claim where it does not and naming the deliverable, the executable and the implementation; the report of each deliverable that no executable runs, as a library function is; and theorems stating what the check decides.

Modules: `LeanIntent/Execution.lean` (the value, the search with its theorems, and the decision with its theorems, which import no more of Lean than the rest of the core), `LeanIntent/Execution/Code.lean` (which compiled declarations are an implementation's code, which imports nothing), `LeanIntent/Execution/Read.lean` (reading the build, which imports all of Lean) and `LeanIntent/Execution/Lake.lean` (reading the executables from Lake's configuration, which imports Lake's).

**Complete in this version:** the value, the search and the decision with their theorems, the reader a gate calls and the reading of Lake's configuration. What an executable does when it runs, beyond which declarations of its compiled code its entry point reaches, is not established; see [What is trusted](#what-is-trusted).

[The implementation check](implementation.md) binds a deliverable to the constant a project records as its implementation, with the proof that the constant fulfils the record. It does not say that a program runs that constant: a project can record and prove `sortProgram` while its executable's `main` calls another function, and every proof the gate reads would still pass. This check closes that gap for each executable a project says runs a deliverable.

## What a project declares

For each executable target that is meant to run a deliverable, one value, in a module that imports the deliverable and that the gate reads:

```lean
import LeanIntent.Execution

/-- The executable `sorter` runs the sorting deliverable. -/
def sorterRuns : LeanIntent.Runs sortingDeliverable where
  executable := `sorter
```

The executable is named as the project's Lake configuration names the target: `` `sorter `` for a `[[lean_exe]]` table of `lakefile.toml` whose `name` is `"sorter"`, or a `lean_exe sorter` of `lakefile.lean`. The reader reads the name as the kernel reduces it to `Name.str` and `Name.num` applied to literals, so write it as a name literal; a name computed by a function, such as one built with `++`, is an error of the reader naming the value. The value names the deliverable in its type and is declared after it, so, like an implementation's value, it enters no answer's text and the confirmations stand. A deliverable that two executables run has two values, one naming each.

A deliverable that no executable is meant to run, such as a library function that other programs call, has none, and the check reports it as run by no executable.

## What it decides

The search (`Execution.reach`) is given the names each name refers to, `refs`, and decides whether a target is reached from a root through them (`Execution.Reaches`). It visits each name once, with a set of the names it has visited, and spends one unit of fuel on each.

| Theorem | What it establishes |
|---|---|
| `reach_reached` | the search reports the target reached only when it is reached |
| `reach_unreached` | the search reports the target unreached only when it is not reached |
| `reach_exhausted` | the search runs out of fuel only when no list of as many names as its fuel holds every name reached |
| `reach_eq_reached_iff` | given such a list, the search reports the target reached exactly when it is reached |
| `reaches_prune_iff` | when every name that refers to a name a predicate keeps is kept too, and the target is kept, the target is reached through the references of the kept names exactly when it is reached through all of them |

The decision (`Execution.findings`) reads the project's deliverables, the implementation recorded for each and those declared awaiting theirs, as [the implementation check](implementation.md#what-a-gate-reads) reports them, the executables (`Execution.Executable`: its name, its root module, whether that module and what it imports declare `main`, and which of the implementations asked about `main` reaches) and the claims (`Execution.Claim`), and lists what is wrong:

- **No deliverable** (`noDeliverable`): a project that declares none has nothing to run, never a pass.
- **A claim tied to no deliverable** (`untied`), naming it: its type names a deliverable the modules read do not declare, or a term in place of a deliverable's constant.
- **A claim naming an executable the project does not declare** (`unknownExecutable`), naming the claim and the executable: an executable the check is not given is never treated as running nothing.
- **An executable with no entry point** (`noEntryPoint`), naming it and its root module: neither the root module nor what it imports declares `main`.
- **A claim of a deliverable with no implementation recorded and none awaited** (`unimplemented`), naming the deliverable and the executable; the implementation check refuses that deliverable too.
- **A claim whose executable's entry point does not reach the implementation** (`unreached`), naming the deliverable, the executable, whose entry point is the `main` its root module imports, and the implementation, by its module and its name.

| Theorem | What it establishes |
|---|---|
| `findings_eq_nil_iff` | for every list of deliverables, implementations, awaited deliverables, executables and claims, the decision finds nothing exactly when there is a deliverable, every executable has an entry point, and every claim names a deliverable of the project and an executable of it, and either the deliverable is declared awaiting its implementation, or an implementation is recorded for it and the entry point of every executable of that name reaches every implementation recorded for it (`Accounted`, stated over the lists and sharing no definition with the decision) |
| `findings_sound` | each finding holds of the lists, and names the claim, executable or deliverable it is about |
| `mem_reached` | the report lists a deliverable, an executable and an implementation as reached exactly when a claim says the executable runs the deliverable, which is the project's and is not declared awaiting its implementation, the implementation is recorded for it, and the entry point of an executable of that name reaches it; so a deliverable declared awaiting its implementation is never listed as reached |
| `mem_awaiting` | the report lists a deliverable and an executable as awaiting exactly when a claim says the executable runs the deliverable, which is the project's and is declared awaiting its implementation |
| `mem_notRun` | the report lists a deliverable as run by no executable exactly when it is the project's and no claim names it |
| `mem_idle` | the report lists an executable as running no deliverable exactly when it is the project's and no claim names it |
| `listed_of_nil` | where the decision finds nothing, each claim is listed as awaiting or, for every implementation recorded for its deliverable, as reached |

The decisions, each made on the owner's behalf, which a later change can reverse:

- **What an executable runs is declared, and checked, rather than inferred from names.** A claim names the executable target. A deliverable no claim names is reported as run by no executable rather than refused, since a library's deliverables are run by its users' programs, and an executable no claim names is reported as running no deliverable. Such an executable may be one whose `Runs` declaration was forgotten: a project whose executable runs a deliverable declares that claim, so that the check reads what the executable runs.
- **A deliverable declared awaiting its implementation is reported as awaiting, never as reached**, even where an implementation is also recorded beside the declaration, which the implementation check refuses.
- **An executable without an entry point is refused whether or not a claim names it**, since a gate that cannot read its entry point can say nothing of what it runs.
- **Every implementation recorded for a claimed deliverable must be reached, by every executable of the name the claim gives.**
- **Reaching is through the code the build compiled, not through every constant a declaration mentions, and the implementation is reached where its compiled code is**. A constant mentioned only in a type or a proof is part of no program, so following it would pass a `main` that uses only the proof that the implementation fulfils its record; and the kernel's value of a `partial` definition, or of a constant `implemented_by` replaces, is not the code that runs. The reader follows the IR the build stored, the code it emitted as C, and counts the implementation reached where the implementation itself, or a copy reduce-arity made of it, is. The next section says what is read and why.

## What a gate reads

`LeanIntent.Execution.Read.check mods exes`, given the project's modules as Lake lists them, the same list given to the other checks, and the executables as Lake's configuration declares them (`LeanIntent.Execution.lakeExecutables`, every `lean_exe` target of the package by its name and root module), reads everything through Lean and Lake, and parses no source text, as its module comment's table states for each input: the deliverables as the confirmation check finds them; the implementations and awaited deliverables as `LeanIntent.Implementation.Read.check` reports them; every constant of the modules whose type reduces to `Runs _`, the deliverable its type names and the executable its value names, reduced by the kernel; and, for each executable, the environment Lean imports from its root module alone, which holds that module and what it imports and nothing else. The entry point is that environment's `main`: Lean's code generator writes the program's entry point for the one module that declares `main`, and two modules that both declare it cannot be imported together.

From `main`, the reader walks the IR the build stored, as Lean finds it for each declaration (`IR.findEnvDecl`, [`Lean/Compiler/IR`](https://github.com/leanprover/lean4/tree/v4.35.0/src/Lean/Compiler/IR)): each declaration leads to those its IR body calls (`fap`) or makes a closure of (`pap`), read by a match over every constructor of the IR's syntax, so that a constructor a later Lean adds fails the library's build rather than going unread (`irRefs`). A declaration with no stored IR, or whose IR declares it `extern`, implemented in another language, leads nowhere. A file outside Lean's module system stores its IR in its `.olean`, and a file of the module system in its `.ir`, which Lean's import loads; where a module's `.ir.sig` is missing, Lean reads instead the opaque declarations its `.olean` keeps, which lead nowhere, so the check can only refuse, and where the `.ir.sig` is present and the `.ir` missing, reading the executable is an error. The reader sets no environment extension's state and runs no part of the compiler: the IR is the code the build emitted, with types and proofs erased, `partial` definitions, `implemented_by` and `csimp` replacements already resolved, and functions already inlined.

The implementation is reached where its compiled code is (`isCompiledCodeOf`, in `LeanIntent/Execution/Code.lean`): the implementation `c` itself, or a declaration with stored IR that the environment holds no constant of and whose name is that of `c`'s compiled code followed by `_redArg`. Where a declaration has a parameter its body does not use, reduce-arity names the copy of its body over the parameters it uses that way and makes the declaration a wrapper that every caller inlines, so a polymorphic implementation, or one taking a proof, is called only through `c._redArg`, and calling it runs `c`'s code (a decision made on the owner's behalf). No other declaration the compiler makes counts: a closed term extracted from `c`'s code, `c._closed_i`, is shared with every later declaration that holds the same term, so reaching it need not run `c`; a lambda lifted out of `c`'s code is reached only where a caller inlined `c`; and a specialization of `c`, `c._at_.caller.spec_i`, is recorded only in a cache that Lean keeps private to its compiler. A constant of the environment other than the implementation is never counted, whatever its name (`isCompiledCodeOf_const`), and `isCompiledCodeOf_iff` states the rule in other terms. The module comment of [`LeanIntent/Execution/Read.lean`](../LeanIntent/Execution/Read.lean) cites the lines of Lean's source each of these facts is read from.

The walk refuses a claim although the program runs the implementation in these cases:

- an implementation the compiler inlined where it is called, whatever it then reaches of the implementation's lambdas or closed terms: mark the implementation `@[noinline]`;
- an implementation the compiler specialized at a caller, such as one with an instance parameter that `main` calls with a known instance: mark the implementation `@[nospecialize]`, under which the compiler specializes none of its parameters;
- an implementation that `implemented_by` or a `csimp` theorem replaces, whose callers' code calls the replacement: record as the deliverable's implementation the constant the program runs;
- an implementation reached only through a module initializer, which the program runs before `main` and which `main`'s code does not call: a known false refusal, which the check does not remove.

An implementation marked `@[extern]` is reached where code that `main` reaches calls it, and its code in another language is trusted.

It follows only declarations of the modules whose imports reach the module that declares the implementation (`importersOf`), since a declaration's code calls only declarations of modules its own imports reach; `reaches_prune_iff` states that this loses no path, given that fact about Lean, which is trusted. So the reader never reads the code of Lean's own libraries, and a gate's cost grows with the project's modules between the implementation and the entry point. For each declaration kept that is the implementation's compiled code, the walk records the implementation too, an entry that stands for that fact rather than for a call. The verdict is `Execution.reach` over what the walk recorded, with fuel `2 ^ 64`, and the implementation is asked for by its module and its name, so a constant of the same name in another module is not it. It returns a `Report`:

| Field | What it holds |
|---|---|
| `findings` | what is wrong; empty exactly when every claim holds, as above |
| `reached` | each deliverable, executable and implementation such that a claim says the executable runs the deliverable and its entry point reaches the implementation |
| `awaiting` | each deliverable and executable such that a claim says the executable runs the deliverable, which is declared awaiting its implementation |
| `notRun` | each deliverable that no claim says an executable runs |
| `idle` | each executable that no claim names |

A gate runs it with the other checks, from the project's top level under `lake env lean gate.lean`, loading the package with Lake's own loader, as lean-intent's `tools/check.lean` does:

```lean
import Lake
import Lake.Load.Package
import LeanIntent.Execution.Lake
import LeanIntent.Execution.Read
import MyProject.Deliverables
import MyProject.Implementations
import MyProject.Runs

/-- The project's package, as Lake's loader reads `lakefile.toml`. -/
def projectPackage : IO Lake.Package := do
  let (elan?, lean?, lake?) ← Lake.findInstall?
  let some lean := lean? | throw <| IO.userError "Lake found no Lean installation"
  let some lake := lake? | throw <| IO.userError "Lake found no Lake installation"
  let lakeEnv ← match ← (Lake.Env.compute lake lean elan?).toBaseIO with
    | .ok env => pure env
    | .error e => throw <| IO.userError e
  let some pkg ← (Lake.loadPackage { lakeEnv, wsDir := ← IO.currentDir,
      relConfigFile := "lakefile.toml", configLang? := some .toml }).toBaseIO
    | throw <| IO.userError "Lake could not load lakefile.toml"
  return pkg

run_meta do
  let mods := #[`MyProject.Deliverables, `MyProject.Implementations, `MyProject.Runs]
  let exes := LeanIntent.Execution.lakeExecutables (← projectPackage)
  let run ← LeanIntent.Execution.Read.check mods exes
  unless run.findings.isEmpty do
    throwError "the executables do not run what they claim: {repr run.findings}"
  for d in run.notRun do
    logInfo m!"{d} is run by no executable"
```

Every executable's root module must be built before the gate runs (`lake build` of the executables, or of their root modules), since the reader imports it.

## Worked examples

- [`LeanIntentExamples/Execution.lean`](../LeanIntentExamples/Execution.lean): the sorting deliverable of [the implementation check's example](implementation.md#worked-examples), claimed to be run by an executable `sorter` (`sorterRuns`); the decision, given what the build shows, finds nothing when `sorter`'s `main` reaches the program and lists it as reached, and refuses by name an entry point that does not reach it, an executable with no entry point, a claim naming an executable the project does not declare, a claim tied to no deliverable, a claim of a deliverable with no implementation, and a project with no deliverable; a claim of the deliverable while it awaits its implementation passes and is listed as awaiting, not reached; and with no claim, or no executable, the deliverable is listed as run by none. Over literal names, it states which compiled declarations the reader counts as an implementation `c`'s code: reduce-arity's copy `c._redArg`, and its copy `c._redArg._redArg`, but not the closed terms `c._closed_0` and `c._redArg._closed_0`, a constant named `c._redArg`, `f._at_.c.spec_0`, a specialization of `f` made inside `c`, the specializations `c._at_.main.spec_0` and `c._at_.main.spec_0._redArg` of `c` itself, or the lifted lambda `c._lam_0`. A worked example holds no build, so the reader is not run by it.

## What is trusted

- That the IR the build stored for each declaration is the IR it emitted as C, both written by the same `lean` run, and that the C compiler and Lean's runtime run that code.
- That a declaration's code calls only declarations of modules its own imports reach, on which pruning rests (`reaches_prune_iff` takes it as a hypothesis): Lean compiles a module in the environment of what it imports and what it declared before, and stores the declarations the compiler makes in that module's IR.
- That a declaration the environment holds no constant of, named as reduce-arity names its copy of a declaration (that declaration's name followed by `_redArg`), is that copy, read from Lean v4.35.0's source (`Lean/Compiler/LCNF/ReduceArity.lean` line 172, the one place in Lean's source that makes such a name), and to be read again at each upgrade of the toolchain. No other name is relied on: every other declaration the compiler makes is refused, and a constant of the project is never counted for another.
- That reaching is what is meant by running. A `main` that reaches the implementation can still choose at run time not to call it, such as in a branch its input never takes; code that the program runs before `main`, such as module initializers, is not read, so an implementation reached only through one is refused; and the compiled code of the implementation itself is trusted to compute its definition, as [the implementation check](implementation.md#what-is-trusted) states, including the code in another language of an implementation marked `extern` (one that `implemented_by` replaces is refused, as above).
- That the executables given to `Read.check` are the project's, each with the root module Lake builds it from. `lakeExecutables` reads them from the package a gate loads with Lake's loader; a claim naming an executable the check is not given is refused, so an executable left out can only make claims fail, while one given with the wrong root module would be read in another program's environment. An executable built by a custom Lake target rather than `lean_exe` is not read, so a claim naming it is refused.
- That the modules given are all the project's, as for the other readers: a claim in a module left out is not read, so its deliverable is reported as run by no executable.
- That every declaration the reader reads was checked by Lean's kernel, and the kernel's reduction, as [the implementation check](implementation.md#what-is-trusted) states.
