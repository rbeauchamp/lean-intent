# The theorems a deliverable relies on, where the proof check builds them

**The theorems a deliverable relies on** (`LeanIntent.Required`, `LeanIntent.Proof`, `LeanIntent.Required.Read`): a value a project declares that names, for one deliverable, theorems the intent-first procedure requires of it, each by its proof; and the decision a project's gate runs, with the confirmation and implementation checks, that refuses the project unless each deliverable is named by such a value and each such theorem, each deliverable and each value recording an implementation is declared in a module its build lists, read from Lean's environment and from Lake's own list of the modules the build compiles, with theorems stating what it decides.

Modules: `LeanIntent/Required.lean` (the value, the decision and its theorems, which import no more of Lean than the rest of the core) and `LeanIntent/Required/Read.lean` (reading the build and Lake's list of its modules, which imports all of Lean).

**Complete in this version:** the value, the decision with its theorems, and the reader a gate calls, with the reader of Lake's list. That every theorem the procedure requires is named is not established, and nor is what each named theorem states; see [What is trusted](#what-is-trusted).

The intent-first procedure has a project prove theorems it then relies on: a record's adequacy obligations, the comparison between a second model's blind formalization and the record, the answers a deliverable keeps and the proof that its implementation fulfils the record. A theorem is checked only where the project's proof check, the check it runs on every change to establish its proofs, builds the module that declares it. In an adopting project the comparison theorems sat in an uncommitted scratch file that its proof check never ran, so the step read as done while nothing was checked. A written rule to commit them where the check builds them depends on whoever follows it; this check makes the failure a refusal.

## What a project declares

For each deliverable, at least one value, in a module the proof check builds that imports the deliverable and the theorems it lists:

```lean
import LeanIntent.Required

/-- The theorems the procedure requires of the sorting deliverable, each by its name. -/
def sortingRequired : LeanIntent.Required sortingDeliverable where
  theorems := [⟨sorting_o2⟩, ⟨sorting_o3⟩, ⟨sorting_o4⟩, ⟨sorting_o5_eq⟩, ⟨sorting_verdicts⟩,
    ⟨sorting_narrower⟩, ⟨nilSort_separates⟩]
```

Each entry is a `LeanIntent.Proof`, a proof of some proposition, written as the theorem's name, `⟨name⟩`, or `⟨@name⟩` where the theorem's first arguments are implicit, since Lean would otherwise apply it to arguments it infers. Lean checks, when the value is declared, that each entry is a proof and that its name is a constant the module imports. A value lists at least one theorem: the field `nonempty` holds the proof that the list is not empty, which its default, `simp`, proves of a list written out, so an empty list is no value of the type (`empty_unrepresentable` in the worked example). A deliverable may have several values, for example one beside its obligations and one beside the comparison with the blind formalization, each in the module that holds its theorems.

What to list is the procedure's to say: [intent-first](../skills/intent-first/SKILL.md) has a project list every theorem it asks for, its obligations, the comparison with the blind formalization and the consequences it states among them. The answers a deliverable keeps, and the proof that its implementation fulfils the record, need no entry: the deliverable and the value of `LeanIntent.Implementation` hold them, and the decision reads where each of those is declared.

## What it decides

The decision (`Required.findings`) reads the module names the build lists, the deliverables and the values recording implementations, each by the module Lean's environment records as declaring it (`Implementation.Constant`), and, for each value of `Required`, the deliverable its type names and what it lists, each entry read as a theorem by its module and its name, a constant that is not a theorem, or a term (`Required.Entry`, `Required.Cited`). It lists what is wrong, and `Finding.message` says, for each, what the project declares or moves to clear it:

- **A deliverable declared in a module the build does not list** (`deliverableUnbuilt`), naming it and the module: the proof that its record keeps its answers is checked where that module is built.
- **A value recording an implementation declared in a module the build does not list** (`implementationUnbuilt`), naming it and the module: likewise, for the proof that the implementation fulfils the record.
- **A deliverable no value of `Required` names** (`undeclared`), naming it: the refusal says to declare a value of `LeanIntent.Required` for it listing its theorems.
- **A value whose type names no deliverable of the project** (`untied`), naming it.
- **An entry that is a term rather than a constant** (`notConstant`), naming the value: a term names no declaration whose module can be read.
- **An entry that is a constant but not a theorem** (`notTheorem`), naming the value and the constant, such as a definition or an axiom.
- **A theorem declared in a module the build does not list** (`unbuilt`), naming the value, the theorem and the module: the proof check does not check it.

| Theorem | What it establishes |
|---|---|
| `findings_eq_nil_iff` | for every list of module names, deliverables, values recording implementations and entries, the decision finds nothing exactly when each deliverable and each such value is declared in a module the list holds, each deliverable is named by an entry, each entry names a deliverable, and each thing an entry lists is a theorem declared in a module the list holds (`Located`, stated over the lists and sharing no definition with the decision) |
| `findings_nothing` | a project that declares no deliverable, no value recording an implementation and no value of `Required` is refused nothing, whatever the build lists |
| `undeclared_mem`, `unbuilt_mem` | a deliverable no entry names is refused, naming it; a theorem an entry lists, declared in a module the list does not hold, is refused, naming the value, the theorem and the module |
| `findings_sound` | each finding holds of the lists, and names the deliverable, value, theorem or module it is about |
| `mem_theorems` | the report lists a theorem with a value exactly when that value's entry lists it as a theorem |
| `Required.nonempty` | a value of `Required` lists at least one theorem |

The decisions, each made on the owner's behalf, which a later change can reverse:

- **Every deliverable names its theorems.** The procedure requires a deliverable's obligations and its comparison before the deliverable is confirmed, and a theorem nothing names is one no check finds, so a deliverable no value names is refused, and the refusal says what to declare. A project that declares no deliverable, no implementation and no value of `Required` is refused nothing (`findings_nothing`), so adopting the check changes nothing for a project that has declared nothing yet.
- **Where a theorem lies is the module Lean's environment records as declaring it**, never its name. One environment holds one declaration of a name: importing a second module that declares a name the environment already holds is an error (`throwAlreadyImported` in Lean v4.35.0's `src/Lean/Environment.lean`, lines 2069 to 2072, called at line 2344), so a theorem of the same name in a file the build does not list cannot pass for one in a module it lists (`sameName_refused` in the worked example).
- **An entry is a constant Lean records as a theorem, and nothing else.** A term could hold a proof under any wrapper, so the decision accepts this closed form and refuses every other by name rather than reading inside it.
- **A module counts as built only where the build's own list names it.** Lake also builds a module that a listed one imports from another library, but its list does not name it, and an import Lean resolves to a compiled file Lake does not manage is not built at all (see [the README's section on upgrading](../README.md#upgrading-from-import-leanintent)); so a theorem in a module of another library is refused unless the gate also gives that library's list, which it does only when the proof check builds that library's modules.

## What a gate reads

`LeanIntent.Required.Read.check mods built` reads the deliverables, the values recording implementations and the values of `Required` from the modules `mods`, as the confirmation and implementation checks read theirs, and decides them against `built`, the module names the build lists; its module comment's table states how each input is read. Each entry of a value of `Required` is reduced by `Render.readWhnf`, through Lean's kernel, to `Proof.mk`'s application, and its proof read as the value holds it: a constant once its metadata is removed, and otherwise a term. Where Lean's elaborator abstracted a proof term into an auxiliary theorem of the value's own module, such as `myRequired._proof_1`, the value holds that theorem's constant and the reader reads it as that theorem, declared in that module; this was observed at Lean v4.35.0 for an entry written as a theorem applied to an argument, while an entry written as a constructor's application was read as a term. A value that is an opaque constant or an axiom does not reduce to its constructor's application and is an error naming it, and an unsafe or partial one is an error too, since it is found through `Confirmation.Read.declaredIn`, which requires safety `safe` (`Confirmation.Read.proofSafe_iff`). It returns a `Report`:

| Field | What it holds |
|---|---|
| `findings` | what is wrong; empty exactly when every required theorem lies in a module the build lists, as above |
| `theorems` | each theorem a value lists, with that value and the theorem's module and name: the account of which module holds each theorem, for the project's report |

### The module names the build lists

The check is only as good as `built`, which must be the modules the project's proof check compiles. A gate reads them from Lake, which owns them, through `Read.queryModules`, which reads what `lake query --json` prints:

- **Which libraries.** The proof check builds the targets its command names: `lake build` with no argument builds the package's default targets (`defaultTargets` in `lakefile.toml`, `@[default_target]` in `lakefile.lean`; `resolveDefaultPackageTarget` in `Lake/CLI/Build.lean`, lines 115 to 118, at Lean v4.35.0), and `lake build <target>` the targets it names. A library target given with no facet selects its `default` facet (`resolveConfigDeclTarget`, lines 89 to 103), which builds the facets in its `defaultFacets`, `#[LeanLib.leanArtsFacet]` unless its configuration says otherwise (`Lake/Config/LeanLibConfig.lean`, line 100; `LeanLib.recBuildDefaultFacets` in `Lake/Build/Library.lean`, lines 177 to 180). For each library whose `leanArts` facet the proof check builds this way, the gate asks Lake for that library's modules; a library whose configuration leaves `leanArts` out of what the check builds is not one of them, and its modules are not built by it.
- **Which modules.** `lake query --json @/<library>:modules` prints the modules that library's `leanArts` facet builds: those its `globs` name, read over the working tree (`LeanLib.getModuleArray`, `Lake/Config/Module.lean`, lines 61 to 66), and, recursively, the modules of the same library they import (`LeanLib.recCollectLocalModules`, `Lake/Build/Library.lean`, lines 31 to 61, the `modules` facet at lines 63 to 65); `LeanLib.recBuildLean` (lines 67 to 72) builds each module that facet lists. The query builds nothing, since the `modules` facet is not buildable. It prints one line for each target (`query` in `Lake/CLI/Main.lean`, lines 992 to 1002), each a JSON array of the module names (`formatQuery`, `Lake/Config/OutFormat.lean`, lines 76 to 80; `ToJson Module`, `Lake/Config/Module.lean`, line 22), each name written by Lean's `ToJson Name` (`src/Lean/Data/Json/FromToJson/Basic.lean`, lines 174 to 187).
- **Reading them.** `Read.queryModules` reads each line with Lean's JSON parser and each name with Lean's own decoding, `Name.fromJson?`, which reads a string as Lean's name literals write a name, splitting it at each dot outside `«` and `»` (`String.toName`, `src/Init/Meta/Defs.lean`, lines 1225 to 1248, at Lean v4.35.0), and accepts a name only where encoding it again gives back the very string. A module whose name Lean writes without the `«` and `»` its components need, which Lean's own account of `Name.toString` names (names holding `»`, and names whose first component starts with `#` or `?`, which it leaves unescaped, lines 229 to 254), is an error naming it, never a different name; such a project gives `built` from Lake's own module values instead, for example by Lake's API in its gate. Output that lists no module at all is an error, since it would leave every theorem unbuilt.

Run the query in the proof check's own checkout, after its build. A glob finds every file in the working tree, committed or not, so in a working tree holding a file that is not committed Lake's list names its module; in a checkout of a commit, which a validation gate builds, the file does not exist, so a theorem in it is not found and a value listing it does not build.

A gate runs the three checks on the same build, with the build's module names as the modules they read, so that every deliverable it reads lies in a module the build lists:

```sh
lake build
lake query --json @/MyProject:modules > .lake/built-modules.json
lake env lean Gate.lean
```

```lean
import LeanIntent.Confirmation.Read
import LeanIntent.Implementation.Read
import LeanIntent.Required.Read
import MyProject.Deliverables
import MyProject.Implementations
import MyProject.Comparison

run_meta do
  let built ← match LeanIntent.Required.Read.queryModules
      (← IO.FS.readFile ".lake/built-modules.json") with
    | .ok built => pure built
    | .error e => throwError "the build's module list cannot be read: {e}"
  let confirmed ← LeanIntent.Confirmation.Read.check built
  let implemented ← LeanIntent.Implementation.Read.check built
  let required ← LeanIntent.Required.Read.check built built
  unless confirmed.findings.isEmpty do
    throwError "the deliverables are not confirmed: {confirmed.findings.length} findings"
  unless implemented.findings.isEmpty do
    throwError "the deliverables are not implemented: {repr implemented.findings}"
  unless required.findings.isEmpty do
    throwError "required theorems lie outside the build:\n{"\n".intercalate (required.findings.map (·.message))}"
```

Each check refuses a module given that the gate does not import, so the gate imports every module the build lists, here through the modules that import the rest.

## Worked example

[`LeanIntentExamples/Required.lean`](../LeanIntentExamples/Required.lean): the sorting deliverable of [the confirmation check's example](confirmation.md#worked-examples), with a value naming its obligations, the verdicts of its degenerate subjects and two theorems comparing its record with another reading (`sortingRequired`); a value listing no theorem cannot be declared (`empty_unrepresentable`); and the decision, given what the build shows, finds nothing and lists each theorem by its module and its name, finds nothing where nothing is declared, and refuses by name a deliverable no value names, a theorem in a scratch module the build does not list, a theorem of a listed one's name declared in such a module, the deliverable or the implementation's value declared in such a module, a value tied to a deliverable the project does not declare or to a term, a term, and a constant that is not a theorem. A worked example holds no build, so the reader is not run by it; it was observed at Lean v4.35.0 on a project depending on this library, whose gate read Lake's list for its default library with `queryModules`: it listed each theorem by its module, refused a theorem of a library the default targets do not build though a listed module imports it, a theorem of a dependency, a definition, a term and a deliverable no value names, each with the message above, and gave an error on an unsafe value, an opaque constant and an axiom of the type, while reading a list joined by `++` and an entry defined by name as the values they reduce to.

## What is trusted

- That `built` is the list of modules the project's proof check builds. The gate gives it; read from Lake as above it is Lake's own list for the libraries named, and which libraries those are follows from the proof check's command, which the gate's author reads. A list naming a module the check does not build lets a theorem in it pass.
- That the modules given to `Read.check` are the project's, the same list given to the confirmation and implementation checks: a deliverable in a module left out is not asked about, here as there.
- That every theorem the procedure requires is listed. The decision reads what the values list, and a theorem no value lists is not read; the procedure's skill says what to list, and review reads it.
- That each listed theorem states what the procedure asks of it. The decision reads where a theorem lies, not its statement, which review reads.
- That a theorem's proof rests only on axioms the project accepts, and that Lean's kernel checked it, as the confirmation and implementation checks trust for the proofs they read: `sorry` is an axiom (`sorryAx`) that a build with warnings as errors refuses and `#print axioms` lists, and the option `debug.skipKernelTC` skips the kernel's check. A project's gate audits the axioms as it audits its other proofs.
- That Lean's kernel reduction preserves the type and meaning of the admitted declaration, as [the implementation check's document](implementation.md#why-the-reader-requires-safe-definitions) sets out for the reader both share.
- That a name whose encoding gives back the string Lake printed is the name Lake printed it from, which fails only where two names print as one string. `Name.toString` writes the names that can appear in source files so that they read back as themselves, and Lean's own account of it names those that might not; the reader refuses each whose decoding does not give back its string.
- That every module a listed theorem's module imports was built from the project's committed source. A listed theorem's proof may use theorems of the modules it imports, as an entry written as a theorem applied to arguments does through the auxiliary theorem Lean makes of it; Lake builds those imports, but an import Lean resolves to a compiled file Lake does not manage, such as one left in a build directory, is not rebuilt, as [the README's section on upgrading](../README.md#upgrading-from-import-leanintent) sets out.
