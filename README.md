# lean-intent

A Lean library for writing what an owner wants as formal properties, and for checking that those properties are adequate, before any code is written.

A proof shows that code meets its specification, never that the specification says what its owner meant. A specification that misses the owner's intent is a bug of the same standing as code that misses its specification. This library gives a Lean project, and the coding assistant working in it, the means to state what an owner wants as formal properties, to check that they are adequate before any code is written, to have the owner confirm a plain restatement of them, and to prove that the code meets them.

## The owner and the agents

The method this library serves divides the work between a project's owner and its agents: the owner states and confirms a deliverable's contract, through a plain restatement of their intent, and decides what it leaves open that is theirs to decide, and the agents derive and decide everything below it on the owner's behalf. [capture-intent](skills/capture-intent/SKILL.md) states that division, in its section on questions, consequences and unequal minds, and [intent-first](skills/intent-first/SKILL.md) applies it to intent records. In a record, the contract's preconditions on its inputs and the facts about the world it relies on are the record's domain hypotheses, its postconditions on its outcomes and mission results are its properties, and the plain restatement the owner confirms is the record's rendering. Each recorded answer shows whether it is the owner's own or a decision made on the owner's behalf through the owners' log ([`docs/owners-log.md`](docs/owners-log.md)): an answer statement names who gave it, a principal acting as owner or one acting under the delegation it names, and `LeanIntent.Trace` decides whether that delegation traces back to a declared owner. The answers a project keeps against its revisions (`LeanIntent.Answer`) name no author; `LeanIntent.Attributed` pairs each with who gave it, and `LeanIntent.Confirmation` ties that, and what a record says of who settled each thing, to the log and to the revision each applies to ([`docs/confirmation.md`](docs/confirmation.md)). A rendered record says who settled each thing, as the record holds it: confirmed by the owner, derived from what the owner confirmed, decided on the owner's behalf, left to the owner as a fork, or not settled ([who settled each thing](docs/who-settled.md)).

## The method

The method this library serves, intent-first, ships with it as two agent skills under [`skills/`](skills/), used in this order:

1. [capture-intent](skills/capture-intent/SKILL.md) turns an owner's words into an account of what is wanted that another agent can act on, for any project and any receiver. It is the method's first stage.
2. [intent-first](skills/intent-first/SKILL.md) carries one deliverable of a Lean project from that account to an intent record written with this library, proved adequate, read a second time blind and checked against a restatement of the owner's intent that the owner confirms, and only then to code proved against the record.

Give your coding agent both: an agent that loads skills from a directory takes each skill's whole folder, its references included, and one that does not reads each `SKILL.md`, which names the files beside it that it uses.

## Features

Each feature of the library has a document of its own in [`docs/`](docs/): what the feature gives, the modules that hold it, what of it is complete, what it establishes, its worked examples and what it trusts. Start with [the intent record](docs/intent-record.md).

Every claim the library makes about itself is a theorem Lean's kernel checks, resting only on Lean's own axioms, except the assumptions [What is trusted](#what-is-trusted) lists, below and in each feature's document. The repository has no tests. Work not yet built is each a separate issue of this repository, and a feature's document names those that extend it.

## Using it

The library depends on nothing beyond Lean's own libraries, and builds on the Lean release `lean-toolchain` names (`v4.35.0`). Add it to a Lake project's `lakefile.toml`:

```toml
[[require]]
name = "lean-intent"
git = "https://github.com/rbeauchamp/lean-intent"
rev = "main"
```

Then write the intent record for one function, before its code:

```lean
import LeanIntent.Obligations
import LeanIntent.Degenerate
open LeanIntent

def Sorted (l : List Int) : Prop := l.Pairwise (· ≤ ·)

def sorting : IntentRecord (List Int → List Int) where
  shape := .function _ _
  dom := []
  props := [⟨"sorted", fun f => ∀ l, Sorted (f l)⟩, ⟨"rearranges", fun f => ∀ l, (f l).Perm l⟩]
  vocab := [⟨"Sorted", List Int, Sorted⟩, ⟨"Perm", List Int × List Int, fun p => p.1.Perm p.2⟩]
```

and prove its obligations: `O2 sorting`, `O2Run sorting`, `O3 sorting`, `O4 sorting` and `O5 sorting .eq`. Each `Oi r` is the conjunction of the goals its former computes (`o2 r` and the rest), and `oi_correct` turns it into the intended proposition, which is usually the easier form to prove. O1 holds of every record by construction (`o1_wellTyped`). Then state and prove the degenerate check's verdicts, `Verdicts sorting [false, false]`: neither the function returning the empty list nor the identity meets the corrected record. [`LeanIntentExamples/Sorting.lean`](LeanIntentExamples/Sorting.lean) does all of this, and then proves an implementation fulfils the record through the refinement link.

There is no module that imports all the others: a project imports the modules whose declarations it uses, which each feature's document names.

## Module files

Every Lean file of the library is a `module` file, so a `module` file of a project can import each of the library's modules; Lean refuses a `module` file's import of a file that is not one. A file that is not a `module` file imports them as before, and sees every body, as it did. `tools/check.lean` refuses a file of the library that is not a `module` file (its rule `LEAN-MODULE`).

What a `module` file that imports the library sees of a declaration is stated at the declaration:

- Every declaration is public except those marked `private`.
- A program is not exposed: a definition whose type is in one of Lean's monads for elaboration or for input and output (`MetaM`, `CoreM`, `TermElabM`, `CommandElabM`, `IO`). These are the readers of the checks a project runs after its build (`LeanIntent.Confirmation.Read`, `LeanIntent.Implementation.Read`, `LeanIntent.Execution.Read`), the two imports of a build's modules into a program (`LeanIntent.Imported`), the rendering, the audit of declared types' codes and the deriving handler. A project calls them. Each that is handed an environment begins with the library's guard (`LeanIntent.asking`, in `LeanIntent/Loaded.lean`): it throws, before it asks Lean anything, in an environment in which the state of Lean's environment extensions is not loaded, as one a program imported with Lean's `importModules` by default is. A `module` file that imports the library without `import all` cannot unfold one; what the library proves of a program, as `LeanIntent.CodeAudit.isCarrier_eq` does, it proves in the module that declares the program.
- Every other definition carries `@[expose]`, so an importer can unfold it: the definitions of the theory, which statements and proofs unfold, and the functions the programs are built from, which the library's theorems are about. The one exception is `LeanIntent.Execution.Read.bodyRefs`, a `partial` definition: Lean gives no proof its body, in any module, so there is nothing to expose. Lean itself exposes an abbreviation and an instance. Where the library derives an instance that a proof reduces (`DecidableEq`, `BEq`, `Inhabited`), the `deriving` clause exposes it (`deriving @[expose] DecidableEq`); an instance of `Repr` it derives is not exposed. A theorem gives its statement.
- What Lean runs while it elaborates a project's file is marked `meta`: the macro `chars!`, the registration of the deriving handler (`LeanIntent.Declared`) and the commands that show a rendering (`LeanIntent.Render`). The programs those two modules register also run after a build, as ordinary programs, and a declaration marked `meta` can be called only by one that is. So they are declared, not marked `meta`, in modules of their own, `LeanIntent.Declared.Handler` and `LeanIntent.Render.Text`, which the registering modules import with `meta` as well.
- The code and the isomorphism that `deriving LeanIntent.HasCode` writes for a project's type are exposed definitions, in the project's module. For a type that is not public there, because it is marked `private` or because no `public section` holds it and it is not marked `public`, they are private as the type is, and statements and proofs reduce them as they reduce a public type's. What Lean compiles of them, at `v4.35.0`, depends on whether the scope other modules see holds the library's codes (`LeanIntent.Codes`). It does when the file reaches them through a `public import`, of the library or of a module that imports it publicly, as a file that also derives a public type's code must. Where it does not, Lean compiles all of it. Where it does, not the isomorphism or the instance: Lean's compiler refuses a `module` file's program whose type it reads differently in that scope, which then holds the library's codes and not the private code. The handler leaves what the compiler refuses without compiled code, so in that case a program cannot run the isomorphism, and a definition that computes with such a type's code, or only holds it, must be marked `noncomputable`; Lean names the instance when the mark is missing. In a `module` file, one command that derives a public type together with one that is not is refused, since Lean would make the public type's code private too.

The package sets none of Lake's options `requiresModuleSystem`, `allowNonModules` and `allowImportAll`. The first would have Lake warn a project's file that imports the library without being a `module` file, which a project that builds with warnings as errors could not accept. The last is Lake's permission for another package to import a module's private scope with `import all`. Lake at `v4.35.0` does not check it: the check is commented out in its source (`Lake/Build/Module.lean`). So nothing refuses a project's `import all` of a module of the library, and a project's proofs rest only on what the library's declarations state and expose as long as its files write no such import.

Three things a project's `module` file does itself, the first two because of what Lean's own libraries expose at `v4.35.0`:

- **`import all` of a module of Lean's, where a proof reduces a function of Lean's whose body Lean does not expose.** The case most projects meet: deciding that two codes of declared types are equal compares the types' names with `Lean.Name.beq`, which `Init.Prelude` does not expose. So a `module` file that proves by reduction over the code of a type the project declares, as the verdicts of the degenerate and trivial-witness checks are proved, writes `import all Init.Prelude`. [`LeanIntentExamples/Declared.lean`](LeanIntentExamples/Declared.lean) does, and [`LeanIntentExamples/Cone.lean`](LeanIntentExamples/Cone.lean) shows the same for functions of `Lean.Data.Name`, `Lean.PrivateName` and `Lean.Declaration`. Lean names the function it could not unfold in the error it reports.
- **`:= by rfl` in place of `:= rfl`, where the proof needs such an import.** Lean checks a theorem written `:= rfl` in the module's public scope, which an `import all` does not reach.
- **A second import with `meta`, where the file runs one of the library's programs.** Lean loads the compiled code of an imported module only where it is imported with `meta`. A file that runs a program of the library while Lean elaborates it, as `run_meta` does, writes `meta import` beside `import` for the program's module; Lean's error names the import when it is missing. A program that `lean --run` starts does the same for each module whose programs it runs, and declares `public def main`, since a `module` file's declarations are private unless marked: [`tools/codes.lean`](tools/codes.lean) does both for `LeanIntent.CodeAudit` and `LeanIntent.Imported`. Without the import such a program ends with Lean's report that it found no native implementation of the first program it calls.

## Upgrading from `import LeanIntent`

Earlier versions had two modules, `LeanIntent` and `LeanIntentExamples`, that only imported the others (`LeanIntent` all but those of the rendering). They are removed, because a module that imports every other is a list that every feature edits. A project that writes `import LeanIntent` imports instead the modules whose declarations it uses.

A build that holds no compiled file of the removed module, such as one from a fresh clone, refuses `import LeanIntent`: Lean reports that the object file of module `LeanIntent` does not exist. A build directory made before the upgrade still holds that file, and Lake, for which `LeanIntent` is no longer a module of the package, neither rebuilds nor removes it, so Lean would go on importing it, and through it the library's modules as they were last built, with no error. So delete lean-intent's build directory when upgrading (in a project that requires it, `.lake/packages/lean-intent/.lake`) and build again.

## Adding a feature

A feature adds files of its own and edits no file that every feature shares: its modules under `LeanIntent/`, its worked examples under `LeanIntentExamples/`, and its document under `docs/`. Each Lean file it adds is a `module` file, written as [Module files](#module-files) describes. Lake builds every Lean file under those two directories, since `lakefile.toml` selects each library's modules by a glob over its directory rather than by a list; `tools/check.lean` builds and audits every one, and refuses a library file that no library target selects; and this README lists no feature. So two features in different modules edit no line in common. A feature that builds on an existing worked example imports it from a file of its own, as `LeanIntentExamples/Answers.lean` imports the sorting records, rather than extending that example's file. A worked example shows how a record is written and used, and does not pin what a function returns for chosen inputs, which the feature's module states over every input; the exceptions are the owners' log's example text, which shows the grammar's committed format, and what a decision accepts and refuses, as in `LeanIntentExamples/Trace.lean` and `LeanIntentExamples/Confirmation.lean`, which shows what it names.

## What is trusted

- Lean, its kernel and its three axioms (`propext`, `Classical.choice`, `Quot.sound`).
- That a record's properties, domain hypotheses, vocabulary and shape say what the owner meant. This is the one link no proof reaches; the owner validates it by confirming the record's plain restatement, rendered by `LeanIntent.Render`, and deciding the forks it leaves open, and those answers, with the decisions the agents make on the owner's behalf, are kept by `LeanIntent.Answers` (whether an answer of the owners' log has authority that traces back to a declared owner is decided by `LeanIntent.Trace`, and whether a deliverable's stored answers and statuses agree with the log, and its current revision is confirmed, by `LeanIntent.Confirmation`).
- What each feature's document lists under its own What is trusted.

## Checks

`tools/check.lean` is the repository's one check program; for one of its rules it runs `tools/codes.lean`, which it cannot do itself because it is not built against the library. `lean --run tools/check.lean` builds the library with warnings as errors (a `sorry` is a warning), refuses a library file that no library target of `lakefile.toml` selects and a module a target selects whose file Git's index does not list, so that it builds and audits exactly what a build of the library targets builds, refuses a Lean file that is not a `module` file, refuses a `lakefile.toml` that requires another package, audits every declaration's axioms, refuses compiled library code that starts a process or asks where it runs or what its environment holds, and runs the audit of declared types' codes over every declaration of the library, its worked examples included, accepting a declaration only when every attestation of a declared type's code among its dependencies is one of the form its deriving handler writes, with the code and isomorphism the handler derives from the type's declaration, and it rests on no axiom other than Lean's three, and otherwise refusing it and naming the attestation or axiom (see [the degenerate-subject check](docs/degenerate-subjects.md)), and refuses a declaration, of the library or of a Lean file under `tools/`, that imports modules in a way that leaves the state of Lean's environment extensions unloaded, from which a reader's questions to Lean would be answered with no error (the module comment of [`LeanIntent/Imported.lean`](LeanIntent/Imported.lean) gives the library's two ways to import and what each reads), and refuses a declaration of the library that is handed an environment by its caller unless it begins with the library's guard, which throws where that state is not loaded, takes a proof that it is loaded, or is excepted by name as asking only for constants and module headers ([`LeanIntent/Loaded.lean`](LeanIntent/Loaded.lean)); `lean --run tools/check.lean --tests` lists the repository's tests, which must be none. Its module comment states what each rule decides and what it does not. lean-intent has no CI: the local no-mistakes validation is its merge gate, and its Test step runs both, failing when the listing prints anything (`commands.test` in `.no-mistakes.yaml`). A cloud session cannot run that validation; [`AGENTS.md`](AGENTS.md) says what one has done in its place.

## Design

The obligations are Lean propositions about the record, and the store of a record's statements is Lean's environment, in which a record, once declared, has a fixed value.
