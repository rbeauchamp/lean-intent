# lean-intent

Formal verification proves that code meets its specification, never that the specification says what its owner meant. A specification that misses the owner's intent is a defect of the same standing as code that misses its specification.

`lean-intent` gives a Lean 4 project—and the coding assistant working in it—a library and method to state what an owner wants as formal properties, check that those properties are adequate before any code is written, have the owner confirm a plain restatement, and prove that implementation code fulfills the record.

| Stage / Artifact | Purpose | Owned / Checked by | Details |
|---|---|---|---|
| 1. Intent capture | Turn an owner's words into a clear specification brief | [`capture-intent`](skills/capture-intent/SKILL.md) | [The method](#the-method) |
| 2. Intent record & adequacy obligations | Declare `IntentRecord`; `O1` holds by construction, prove `O2`, `O2Run` (required before confirmation for any subject that can refuse; otherwise proved here when exhibited or deferred to stage 5), `O3`, `O4`, `O5`, and degenerate-subject verdicts (`Verdicts`, `MachineVerdicts` for covered machines such as agents with memory, or the interim check in `intent-first` for types covered by neither) | [`intent-first`](skills/intent-first/SKILL.md), Lean kernel | [Using it](#using-it), [the intent record](docs/intent-record.md), [obligations](docs/obligations.md), [machines](docs/machines.md) |
| 3. Blind formalization & comparison | Independently formalize the owner's raw words in a fresh isolated session with no access to the first record, account, or reasoning; compare both readings in theorems—proving each implication direction (`Meets`) or exhibiting a counterexample, or comparing verdicts on concrete cases—and surface any unresolved differences before confirmation | [`intent-first`](skills/intent-first/SKILL.md), Lean kernel | [The method](#the-method), [`intent-first`](skills/intent-first/SKILL.md) |
| 4. Rendering & owner confirmation | Render the record, definitions, and settlement statuses for the owner to confirm (not for the blind reader), and check `OwnersLog`, delegation (`Trace`), and `Confirmation` | `LeanIntent.Render`, `LeanIntent.Trace`, `LeanIntent.Confirmation` | [The owner and the agents](#the-owner-and-the-agents), [rendering](docs/rendering.md), [`docs/confirmation.md`](docs/confirmation.md) |
| 5. Implementation & refinement | After confirmation, write the implementation and prove fulfillment through the refinement link (`Refines`, `fulfils`, with `Refines.o2Run` supplying `O2Run` only for permitted deferrals—never replacing stage 2's pre-confirmation `O2Run` proof for a subject that can refuse) | `LeanIntent.Refinement`, `LeanIntent.Implementation`, Lean kernel | [Using it](#using-it), [refinement](docs/refinement.md), [implementation](docs/implementation.md) |
| 6. Repository verification | Enforce axioms, `module` files, `CODES`, `NO-COMMENTS`, Regula, `LOADED`/`READERS`, and zero tests | [`tools/check.lean`](tools/check.lean) | [Checks](#checks) |

## The owner and the agents

The method divides work between a project's owner and its agents:

- **Authority split:** the owner states and confirms a deliverable's contract through a plain restatement of their intent and decides what it leaves open that is theirs to decide; the agents derive and decide everything below it on the owner's behalf. [`capture-intent`](skills/capture-intent/SKILL.md) states that division in its section on questions, consequences, and unequal minds, and [`intent-first`](skills/intent-first/SKILL.md) applies it to intent records.
- **Parts of a record:** preconditions on inputs and facts about the world the record relies on are its **domain hypotheses**; postconditions on outcomes and mission results are its **properties**; and the plain restatement the owner confirms is its **rendering**.
- **Owners' log and authority tracing:** each answer statement in the owners' log ([`docs/owners-log.md`](docs/owners-log.md)) names who gave it—a principal acting as owner or one acting under the delegation it names—and `LeanIntent.Trace` decides whether that delegation traces back to a declared owner.
- **Answers, attribution, and confirmation:** `LeanIntent.Answer` keeps answers against revisions without naming an author; `LeanIntent.Attributed` pairs each answer with who gave it; and `LeanIntent.Confirmation` ties both that attribution and what a record says of who settled each item to the owners' log and to the revision each applies to ([`docs/confirmation.md`](docs/confirmation.md)).
- **Settlement statuses:** a rendered record shows who settled each item as the record holds it—confirmed by the owner, derived from what the owner confirmed, decided on the owner's behalf, left to the owner as a fork, or not settled ([who settled each thing](docs/who-settled.md)).

## The method

The method this library serves, intent-first, ships with it as two agent skills under [`skills/`](skills/), used in this order:

1. [`capture-intent`](skills/capture-intent/SKILL.md) turns an owner's words into an account of what is wanted that another agent can act on, for any project and any receiver. It is the method's first stage.
2. [`intent-first`](skills/intent-first/SKILL.md) carries one deliverable of a Lean project from that account to an intent record written with this library, proved adequate, independently formalized a second time blind and compared against the first record (proving each implication direction or exhibiting differences, or comparing verdicts on concrete cases) before checking against a restatement of the owner's intent that the owner confirms, and only then to code proved against the record.

Give your coding agent both: an agent that loads skills from a directory takes each skill's whole folder, its references included, and one that does not reads each `SKILL.md`, which names the files beside it that it uses.

## Features

- Each feature of the library has a document of its own in [`docs/`](docs/): what the feature gives, the modules that hold it, what of it is complete, what it establishes, its worked examples, and what it trusts. Start with [the intent record](docs/intent-record.md).
- Every claim the library makes about itself is a theorem Lean's kernel checks, resting only on Lean's own axioms, except the assumptions [What is trusted](#what-is-trusted) lists (below and in each feature's document).
- The repository has no tests.
- Work not yet built is each a separate issue of this repository, and a feature's document names those that extend it.

## Using it

The library depends on nothing beyond Lean's own libraries and builds on the Lean release named in [`lean-toolchain`](lean-toolchain) (`leanprover/lean4:v4.36.0`). Add it to a Lake project's `lakefile.toml`, replacing `<latest-release-tag>` with a signed release tag from [GitHub Releases](https://github.com/rbeauchamp/lean-intent/releases/latest):

```toml
[[require]]
name = "lean-intent"
git = "https://github.com/rbeauchamp/lean-intent"
rev = "<latest-release-tag>"
```

> [!NOTE]
> A project still on Lean `v4.35.0` pins the last commit on `main` built for `v4.35.0` (`rev = "58608794f9fee126f296da1de21e3afb1fb33c1e"`) until it upgrades.

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

Next, prove the record adequate (and, after confirmation, prove fulfillment):

- **Obligations:** prove `O2 sorting`, `O2Run sorting`, `O3 sorting`, `O4 sorting`, and `O5 sorting .eq`. Each `Oi r` is the conjunction of the goals its former computes (`o2 r` and the rest), and `oi_correct` turns it into the intended proposition (usually the easier form to prove). `O1` holds of every record by construction (`o1_wellTyped`).
- **Degenerate verdicts:** state and prove `Verdicts sorting [false, false]`—neither the function returning the empty list nor the identity meets the corrected record.
- **Worked example:** [`LeanIntentExamples/Sorting.lean`](LeanIntentExamples/Sorting.lean) completes all of these proofs and then proves an implementation fulfills the record through the refinement link.
- **Selective imports:** there is no module that imports all others; a project imports the modules whose declarations it uses, which each feature's document names.

### Upgrading from `import LeanIntent`

Earlier versions shipped two umbrella modules, `LeanIntent` and `LeanIntentExamples`, that only imported the others (`LeanIntent` imported all except those of the rendering). They are removed because a module that imports every other is a central list that every feature edits; projects that wrote `import LeanIntent` now import the specific modules whose declarations they use.

- **Fresh clone:** refuses `import LeanIntent` immediately, because Lean reports that the object file of module `LeanIntent` does not exist.
- **Existing build directory:** a `.lake` build directory made before upgrading still holds `LeanIntent.olean`, and Lake (for which `LeanIntent` is no longer a module of the package) neither rebuilds nor removes it—so Lean would keep importing the stale `.olean`, and through it the older modules, without error.
- **Required cleanup:** delete `lean-intent`'s build directory when upgrading (in a project that requires it, `.lake/packages/lean-intent/.lake`) and build again.

## Module files

Every Lean file of the library is a `module` file, so a `module` file of a project can import each of the library's modules; Lean refuses a `module` file's import of a file that is not one. A file that is not a `module` file imports them as before, and sees every body, as it did. `tools/check.lean` refuses a file of the library that is not a `module` file (its rule `LEAN-MODULE`).

What a `module` file that imports the library sees of a declaration is stated at the declaration:

- **Public by default:** every declaration is public except those marked `private`.
- **Programs are not exposed:** a definition whose type is in one of Lean's monads for elaboration or I/O (`MetaM`, `CoreM`, `TermElabM`, `CommandElabM`, `IO`) is not exposed—namely the post-build readers (`LeanIntent.Confirmation.Read`, `LeanIntent.Implementation.Read`, `LeanIntent.Execution.Read`, `LeanIntent.Required.Read`), the stateless import wrapper (`LeanIntent.Imported`), the rendering, the audit of declared types' codes, and the deriving handlers:
  - A project calls them, and each monadic program handed an `Environment` begins with the library's guard (`LeanIntent.asking` or `LeanIntent.askingIn`, in `LeanIntent/Loaded.lean`), throwing before querying Lean when environment extension state is not loaded (such as an environment imported with Lean's default `importModules`).
  - A `module` file that imports the library without `import all` cannot unfold one; proofs about a program (such as `LeanIntent.CodeAudit.isCarrier_eq`) live in the module that declares it.
- **Exposed definitions and instances:** every other definition carries `@[expose]` so an importer can unfold the theory definitions and functions referenced by theorems. Lean itself exposes an `abbrev` and an `instance`. Where the library derives an instance reduced by proofs (`DecidableEq`, `BEq`, `Inhabited`), the `deriving` clause exposes it (`deriving @[expose] DecidableEq`), while derived `Repr` instances are not exposed. A theorem gives only its statement.
- **`meta` separation for elaboration and runtime:** what Lean runs during elaboration is marked `meta`—the macro `chars!`, the handler registrations (`LeanIntent.Declared`, and `LeanIntent.MachineDeclared` for `deriving LeanIntent.CoveredMachine`), and the rendering commands (`LeanIntent.Render`). Because those programs also run after a build as ordinary programs, and a `meta` declaration can be called only by one marked `meta`, their non-`meta` implementations live in `LeanIntent.Declared.Handler`, `LeanIntent.MachineDeclared.Handler`, and `LeanIntent.Render.Text`, which the registering modules import with `meta` as well.
- **`deriving LeanIntent.HasCode`:** writes exposed code and isomorphism definitions in the project's module:
  - If the derived type is not public (`private`, or not marked `public` outside a `public section`), the generated code and isomorphism are private too, and statements and proofs reduce them just like a public type's.
  - For a non-public derived type, what Lean compiles of its generated code and isomorphism at `v4.36.0` depends on whether public scope holds `LeanIntent.Codes` (via a `public import` of the library or a module publicly importing it, as a file deriving a public type's code must): when absent, Lean compiles all of it; when present, Lean omits compiling the isomorphism and instance (because Lean's compiler refuses a `module` file's program whose type reads differently in public scope).
  - The handler leaves what the compiler refuses without compiled code, so in that case no program can run the isomorphism, and any definition computing with or holding such a type's code must be marked `noncomputable` (Lean names the missing instance when omitted).
  - Deriving a public type and a non-public type in one command is refused, since Lean would make the public type's code private too.
- **`deriving LeanIntent.CoveredMachine`:** writes exposed standalone projection definitions, isomorphism, and instance in the project's module so an importing `module` file reduces them without `import all`:
  - If the structure is not public, they are private and Lean exports no instance whose name is private, so the structure is covered in its own module only; the handler writes them as a `noncomputable section` does, leaving refused definitions without compiled code while statements and proofs reduce them all the same ([`LeanIntentExamples/Machines.lean`](LeanIntentExamples/Machines.lean)).
  - Deriving a public structure and a non-public structure in one command is refused, as for `HasCode`.

The package sets none of Lake's options `requiresModuleSystem`, `allowNonModules`, and `allowImportAll`:

- Setting `requiresModuleSystem` would warn downstream non-`module` importers, breaking builds with warnings as errors.
- `allowImportAll` would allow another package to `import all` a module's private scope. Lake at `v4.36.0` does not check it (the check is commented out in `Lake/Build/Module.lean`), so nothing refuses `import all` of a library module; downstream proofs rest solely on what the library states and exposes as long as downstream files write no such import.

Four things a downstream `module` file does itself (the first two due to what Lean's libraries expose at `v4.36.0`, the fourth due to cross-module unfolding equation generation):

1. **`import all` of a Lean module where a proof reduces a Lean function whose body Lean does not expose:** the case most projects meet is deciding equality of declared-type codes, which compares names with `Lean.Name.beq` (not exposed by `Init.Prelude`), so proofs by reduction over declared-type codes (such as degenerate and trivial-witness verdicts) write `import all Init.Prelude`. [`LeanIntentExamples/Declared.lean`](LeanIntentExamples/Declared.lean) does, and [`LeanIntentExamples/Cone.lean`](LeanIntentExamples/Cone.lean) shows the same for unexposed functions of `Lean.Data.Name`, `Lean.PrivateName`, and `Lean.Declaration`; Lean names the function it could not unfold in its error.
2. **`:= by rfl` instead of `:= rfl`:** needed where a proof relies on such an `import all`, because Lean checks `:= rfl` in the module's public scope, which `import all` does not reach.
3. **Second `meta import` when running a library program:** Lean loads compiled code of an imported module only when imported with `meta`. Files running a library program during elaboration (such as `run_meta`) write `meta import` beside `import` (Lean's error names the missing import); `lean --run` scripts do the same and mark `public def main` since `module` declarations are private by default ([`tools/codes.lean`](tools/codes.lean) does both for `LeanIntent.CodeAudit`). Without `meta import`, Lean reports missing native implementation for the first program called.
4. **`public import` of imported recursive definitions:** when rendering a record or running `LeanIntent.Confirmation.Read` whose meaning reaches an imported recursive definition, import that definition's module (or a module publicly re-exporting it, such as the record's module) with `public import`:
   - In a `module` file, `Lean.Meta.getUnfoldEqnFor?` checks whether a definition's body is exposed in the current module's public scope (`Environment.hasExposedBody`), so a plain `import` (or `import all` without `public`) yields no unfolding equation for an imported well-founded recursive definition and names a structurally recursive definition's unfolding equation privately to the importing module.
   - `LeanIntent.Render.unfoldEqn` ([`LeanIntent/Render/Text.lean`](LeanIntent/Render/Text.lean)) therefore refuses any imported recursive definition whose module is imported without `public` and names `public import` of that module as the direct remedy (publicly importing a record's module works when it re-exports the definition's module).
   - Together with `definitions` and `declSection`, it also catches imported non-exposed recursive definitions exported as `.axiomInfo` (`wasOriginallyDefn`, `isRecursiveDefinition`), distinguishing missing `@[expose]` in the defining module from missing `public import`.
   - Non-`module` files and `Lean.importModules` at its default `.private` import level are unaffected.

## Adding a feature

- **Disjoint module layout:** place new library modules under `LeanIntent/`, worked examples under `LeanIntentExamples/`, and documentation under `docs/`.
- **Automatic glob discovery:** [`lakefile.toml`](lakefile.toml) selects each library's modules by a glob over its directory rather than by a list; `tools/check.lean` builds and audits every one and refuses a library file that no library target selects; and this README lists no features—so two features in different modules edit no line in common.
- **Module and comment standards:** each added Lean file must be a `module` file (per [Module files](#module-files)) and carry zero Lean comments (`NO-COMMENTS`, [ADR-0004](docs/adr/0004-ratcheted-ban-on-lean-comments.md)); non-obvious architectural decisions belong in `docs/` or [`docs/adr/`](docs/adr/README.md).
- **Worked examples policy:**
  - Extend an existing worked example from a separate file (as `LeanIntentExamples/Answers.lean` imports the sorting records) rather than editing the existing example file.
  - Worked examples show how a record is written and used and never pin what a function returns for chosen inputs (which the feature's module states over every input).
  - The exceptions are the owners' log's example text (showing the grammar's committed format) and accept/refuse witnesses for decisions (as in `LeanIntentExamples/Trace.lean` and `LeanIntentExamples/Confirmation.lean`, showing what the decision names).

## What is trusted

- Lean, its kernel, and its three axioms (`propext`, `Classical.choice`, `Quot.sound`).
- Correspondence between a record (`props`, `dom`, `vocab`, `shape`) and what the owner meant—the one link no proof reaches, validated when the owner confirms the plain restatement rendered by `LeanIntent.Render` and decides the forks it leaves open:
  - `LeanIntent.Answers` keeps those answers alongside decisions the agents make on the owner's behalf.
  - `LeanIntent.Trace` decides whether an answer in the owners' log has authority tracing back to a declared owner.
  - `LeanIntent.Confirmation` decides whether a deliverable's stored answers and statuses agree with the log and confirm its current revision.
- What each feature's document lists under its own *What is trusted*.

## Checks

[`tools/check.lean`](tools/check.lean) is the repository's single check program:

```sh
lean --run tools/check.lean
lean --run tools/check.lean --tests
```

| Rule / Mode | What it checks and enforces | Spec / Pin |
|---|---|---|
| `LAKE-CONFIG` | Refuses a `lakefile.toml` that requires another package, a library file unselected by any library target, a library target omitted from `defaultTargets`, and a selected module whose file Git's index omits | [ADR-0001](docs/adr/0001-repository-checks-and-trusted-base.md) |
| `LEAN-BUILD` | Builds every library target with warnings as errors (`sorry` is a warning) | [ADR-0001](docs/adr/0001-repository-checks-and-trusted-base.md) |
| `LEAN-MODULE` | Refuses any tracked `.lean` file that is not a `module` file | [Module files](#module-files) |
| `AXIOMS` | Audits every declaration's axioms, allowing only `propext`, `Classical.choice`, and `Quot.sound` | [ADR-0001](docs/adr/0001-repository-checks-and-trusted-base.md) |
| `PROCESS` | Refuses compiled library code that starts a process or queries where it runs or what its environment holds | [ADR-0003](docs/adr/0003-runtime-process-audit-and-exemptions.md) |
| `CODES` | Keeps `tools/check.lean` independent of the built library by running [`tools/codes.lean`](tools/codes.lean) (which imports `LeanIntent.CodeAudit`) in a child `lean --run` process with `LEAN_PATH` pointing to the built library directory over every declaration of the library and its worked examples; accepts a declaration only when every attestation of a declared type's code or of a declared structure's coverage as a machine among its dependencies is in the theorem form its deriving handler writes, with the exact code and isomorphism (or machine isomorphism) the handler derives from the type's declaration, and the declaration rests on no axiom other than Lean's three, refusing it otherwise and naming the attestation or axiom | [Degenerate check](docs/degenerate-subjects.md), [Machines](docs/machines.md) |
| `NO-COMMENTS` | Runs the pinned `no-comments` binary ([`tools/no-comments.pin`](tools/no-comments.pin), [`.no-comments.json`](.no-comments.json)) enforcing the ratcheted ban on Lean comments against [`tools/comment-ratchet.json`](tools/comment-ratchet.json) | [ADR-0004](docs/adr/0004-ratcheted-ban-on-lean-comments.md) |
| `REGULA` | Stages and builds an isolated out-of-tree `rbeauchamp/regula` checkout pinned in [`tools/regula.pin`](tools/regula.pin) without adding any `[[require]]` dependency to `lakefile.toml`, runs `REGULA_PROOF=<lean-intent-dir> lake exe lint standard-logical` from the isolated build directory, and verifies strict proof-verdict compliance—requiring the exact passing proof verdict for this workspace, full coverage of every library module (with non-zero constants), and an unchanged workspace (including `RG1006` totality, `RG1012` panic-free checks, and `RG2001` kernel replay across all claimed modules) | [`tools/regula.pin`](tools/regula.pin) |
| `LOADED` | Refuses any declaration of the library or under `tools/` that imports modules with environment extensions left unloaded (except `LeanIntent.Imported.stored`, which exposes only stateless header/constant/IR queries with no `Environment`) | [ADR-0009](docs/adr/0009-environment-extension-loading-and-reader-guards.md) |
| `READERS` | Refuses any library declaration handed an `Environment` unless it begins with `LeanIntent.asking`/`askingIn`, requires a `Loaded` proof, or appears in the named `stateless` list | [ADR-0009](docs/adr/0009-environment-extension-loading-and-reader-guards.md) |
| `--tests` | Lists the repository's tests; must print nothing | [ADR-0002](docs/adr/0002-test-listing-and-pinned-lean-tokens.md) |

- **Design rationale:** [ADR-0001](docs/adr/0001-repository-checks-and-trusted-base.md), [ADR-0002](docs/adr/0002-test-listing-and-pinned-lean-tokens.md), [ADR-0003](docs/adr/0003-runtime-process-audit-and-exemptions.md), [ADR-0004](docs/adr/0004-ratcheted-ban-on-lean-comments.md), and [ADR-0009](docs/adr/0009-environment-extension-loading-and-reader-guards.md) (indexed in [`docs/adr/`](docs/adr/README.md)) state what each rule decides and what it does not.
- **CI and local validation:** both [`.github/workflows/check.yml`](.github/workflows/check.yml) (pull requests, pushes to `main`, `workflow_call` from [`.github/workflows/release.yml`](.github/workflows/release.yml) on `v*` tag pushes, and `workflow_dispatch`; see [CONTRIBUTING.md](CONTRIBUTING.md#pull-requests-commits-and-triage)) and local no-mistakes validation (`commands.test` in [`.no-mistakes.yaml`](.no-mistakes.yaml)) run both commands and fail if `--tests` prints anything. A cloud session cannot run that local validation; [`AGENTS.md`](AGENTS.md) says what one does alongside CI.

## Design

The obligations are Lean propositions about the record, and the store of a record's statements is Lean's environment, in which a record, once declared, has a fixed value.
