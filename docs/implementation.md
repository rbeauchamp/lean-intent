# The implementation of a deliverable

**The implementation of a deliverable** (`LeanIntent.Implementation`, `LeanIntent.Implementation.Read`): a value a project declares that names the constant implementing a deliverable, by its module and its name as Lean's environment gives them, together with the proof that it fulfils the deliverable's record, so that the fulfilment a gate reads is of that constant and of no other; and the decision a project's gate runs on those values, read from the finished build, with theorems stating what it decides.

Modules: `LeanIntent/Implementation.lean` (the value, the decision and its theorems, which import no more of Lean than the rest of the core) and `LeanIntent/Implementation/Read.lean` (reading the build, which imports all of Lean).

**Complete in this version:** the value, the decision with its theorems, and the reader a gate calls. That the recorded constant is what a program runs is not established; see [What is trusted](#what-is-trusted).

A proof that an implementation fulfils its intent record binds the code only if what the project declares names that code. A deliverable (`LeanIntent.Deliverable`) holds a record, its explanation and the answers it keeps, which its owner confirms before any implementation exists ([the confirmation check](confirmation.md)), and it names no implementation. Every satisfiable record is fulfilled by some constant, a model of it such as `O2Run` asks for, that no program runs, so a gate that accepted any theorem `r.Fulfilled f` would accept a proof about such a constant, and two programs sharing a record would be told apart by nothing the project declares.

## What a project declares

Once the implementation exists, one value for each deliverable, in a module that imports the deliverable and the implementation with its proof:

```lean
import LeanIntent.Implementation

/-- The sorting deliverable's implementation: the program, and the proof that it fulfils the record. -/
def sortingImplementation : LeanIntent.Implementation sortingDeliverable where
  subject := sortProgram
  fulfils := sortProgram_fulfils
```

The deliverable, its explanation and the owners' log stay as they were confirmed, and the deliverable's module need not import the implementation. The subject is the record's subject, of the record's type: a project whose implementation is read as the subject through a mapping (`LeanIntent.Refines`) records a definition of the subject it maps to, and a polymorphic implementation is recorded through a definition at the record's types, since the decision reads only a constant.

## What the type establishes

The field `fulfils` has the type `d.record.Fulfilled subject`. Lean's kernel checks every declaration: it refuses a definition whose value's type is not definitionally equal to its declared type (`environment::add_definition`, `src/kernel/environment.cpp` of Lean v4.35.0), and an application whose argument's type is not definitionally equal to its binder's, with the arguments before it substituted (`type_checker::infer_app`, `src/kernel/type_checker.cpp`, lines 173 to 187). So a value's proof proves that the record is fulfilled by the very subject the value records.

- A theorem that another constant fulfils the record is accepted as the proof only where the two constants are definitionally equal, as for an alias `def sortAlias := sortProgram`; the proposition is then the same one, and what it proves is that the recorded constant fulfils the record.
- A theorem about a constant that differs, such as a wrapper that returns `[]` for long lists, is refused: Lean reports an application type mismatch, naming the proof, the proposition it proves and the one expected, and the project does not build. This was observed at Lean v4.35.0.
- So a subject can be recorded as the implementation exactly when it fulfils the record (`Implementation.exists_iff`), and the function returning the empty list, which fails the sorting record, cannot be recorded by any proof (`nilSort_unrecordable` in the worked example).
- A theorem elsewhere in the project about another constant, such as `sorting.Fulfilled List.mergeSort`, is no value of this type, and the decision does not read it.

## How it ties to the owners' log, and what it leaves unchanged

A value names its deliverable in its type, the deliverable names its record, and the answers of the project's owners' log name that record and the text of its revision ([the confirmation check](confirmation.md#what-it-decides)). Nothing of the value enters the texts an answer holds: they are computed from the deliverable's explanation and what its meaning reaches (`Render.revisionText`, `Render.consequenceText`), and the value is declared after the deliverable its type names, so nothing the deliverable holds refers to it, since a declaration refers only to constants the environment already holds (`environment::get`, which the kernel's `type_checker::infer_constant` calls, refuses an unknown constant). Recording the implementation, replacing it with another or moving the value to another module therefore changes no answer's text, and the confirmations stand; the confirmation check finds no value of this type, so its report is unchanged too.

Renaming a constant changes the text of every revision and answer whose meaning reaches it, as it always has. A record's meaning reaches no declaration of its implementation where [cone exclusion](cone-exclusion.md) accepts it, and a gate can pass the recorded constant to `LeanIntent.Cone.checkRecord` as the implementation. A consequence the explanation shows may still name a function: in the worked example the explanation reaches `sort`, through the consequence the assistant answered, and never `sortProgram`, the implementation recorded.

## What it decides

The decision (`Implementation.findings`) reads, for each value a project declares, the deliverable its type names and the constant its subject is (`Implementation.Entry`), and lists what is wrong:

- **No deliverable** (`noDeliverable`): a project that declares none has nothing implemented, never a pass.
- **A deliverable no value implements** (`unimplemented`), naming it: nothing then says which code fulfils it.
- **A deliverable several values implement** (`several`), naming it and them, whichever constants they record: the project's declarations would then not tell which program is the deliverable's.
- **A value tied to no deliverable** (`untied`), naming it: its type names a deliverable the modules read do not declare, or a term in place of a deliverable's constant.
- **A value whose subject is not a constant** (`notConstant`), naming it: a term such as `fun l => sort l` names no constant a reader can find.

| Theorem | What it establishes |
|---|---|
| `findings_eq_nil_iff` | for every list of deliverables and of entries, the decision finds nothing exactly when there is a deliverable, each has exactly one entry recording its implementation, and each entry names one of them and records a constant (`Implemented`) |
| `findings_sound` | each finding holds of the deliverables and entries, and names the deliverable or the value it is about |
| `mem_implementations` | the report lists a deliverable with a value and a constant exactly when that value is the one entry recording its implementation, and that constant its subject |
| `implementations_of_nil` | where the decision finds nothing, the report lists every deliverable with its value and the constant, by module and name |
| `Implementation.fulfilled`, `Implementation.exists_iff`, `Implementation.meets` | a value's subject fulfils the record; a subject can be recorded exactly when it fulfils it; and it meets the record wherever the domain hypotheses hold of it |

The decisions, each made on the owner's behalf, which a later change can reverse:

- **One implementation for each deliverable.** A project with two programs for one record declares two deliverables, each with its own value.
- **One constant may implement several deliverables.** Each value's proof is of its own deliverable's record, so a theorem about one record discharges no other, and one program may be what two contracts are about (`oneConstant_accepted`).
- **The subject is a constant, and nothing else.** The decision accepts this closed form and refuses every other by name, rather than reading a term's head or unfolding it, since a term could hold the implementation under any wrapper.
- **The module is read, not written.** Lean's environment records the one module that declares each constant, so the report gives the module and the name of the constant the value holds, and no field written by hand could disagree with it.

## What a gate reads

`LeanIntent.Implementation.Read.check mods`, given the project's modules as Lake lists them, the same list given to `LeanIntent.Confirmation.Read.check`, reads everything from Lean's environment and parses no source text, as its module comment's table states for each input: the deliverables as the confirmation check finds them, every constant whose type reduces to `Implementation _`, the deliverable its type names, the subject of its value reduced by `whnf` to the constructor's application, whose arguments `whnf` leaves as they are (`Meta.whnfCore` and `Meta.unfoldDefinition?`, `src/lean/Lean/Meta/WHNF.lean` of Lean v4.35.0), and the module the environment records for that constant (`Environment.getModuleIdxFor?`). It returns a `Report`:

| Field | What it holds |
|---|---|
| `findings` | what is wrong; empty exactly when every deliverable is implemented as above |
| `implementations` | each deliverable implemented by exactly one value whose subject is a constant, with that value and the constant's module and name |

A value that is an opaque constant or an axiom, which does not reduce to the constructor's application, is an error naming it, never a pass, and so is every unsafe constant of the types the reader looks for, since an unsafe definition may refer to itself and so prove anything, while a safe declaration cannot refer to an unsafe one. A gate runs both checks on the same build:

```lean
import LeanIntent.Confirmation.Read
import LeanIntent.Implementation.Read
import MyProject.Deliverables
import MyProject.Implementations

run_meta do
  let mods := #[`MyProject.Deliverables, `MyProject.Implementations]
  let confirmed ← LeanIntent.Confirmation.Read.check mods
  let implemented ← LeanIntent.Implementation.Read.check mods
  unless confirmed.findings.isEmpty do
    throwError "the deliverables are not confirmed: {confirmed.findings.length} findings"
  unless implemented.findings.isEmpty do
    throwError "the deliverables are not implemented: {repr implemented.findings}"
```

## Worked examples

- [`LeanIntentExamples/Implementation.lean`](../LeanIntentExamples/Implementation.lean): the sorting deliverable of [the confirmation check's example](confirmation.md#worked-examples), implemented by a program written after its record was confirmed (`sortingImplementation`), whose proof is `sort`'s since the two are the same function by definition; the empty-list function cannot be recorded (`nilSort_unrecordable`); and the decision, given what the build shows, finds nothing and lists the program by its module and its name, and refuses by name no value, no deliverable, a second value, a value tied to a deliverable the project does not declare or to a term, and a subject that is a term, while accepting one constant that implements two deliverables. A worked example holds no build, so the reader is not run by it; it was observed at Lean v4.35.0 on the worked example and on values written to attack it, reading the program by its module and its name, refusing a second value, a term as the subject and a term as the deliverable, and giving an error on an axiom and on unsafe values.

## What is trusted

- That the recorded constant is what a program runs. The value says which constant the project's deliverable is, and its proof binds that constant; that an executable's entry point calls it, and that its compiled code computes its definition, which `implemented_by` and `extern` replace with other code, are not established here. Accepted: a project's review reads which constant it records, and the history shows a change of it.
- That every declaration the reader reads was checked by Lean's kernel. The option `debug.skipKernelTC`, and a metaprogram that adds a declaration without checking it (`Kernel.Environment.addDeclWithoutChecking`), skip that check, so a value's proof could then prove nothing. A gate that must not trust this replays the build's declarations through the kernel.
- That a value's proof rests only on axioms the project accepts. Lean's kernel checks the proof relative to the axioms the environment declares, and `sorry` is one (`sorryAx`), which a build with warnings as errors refuses; `#print axioms` lists a value's, and the decision does not, as the confirmation check does not list those of the proofs a deliverable holds. A project's gate audits them as it audits its other proofs.
- That the modules given to `Read.check` are all the project's: a value in a module left out records nothing, so its deliverable is refused as unimplemented, and a deliverable in it is not asked about. A constant whose type is not `Implementation _` once every definition is unfolded, such as a function returning a value of it or a structure holding one, is not found, so it records nothing.
- That `Read` reads what the values are. It only reads constants, through `whnf` and the environment, as its module comment's table says; this is argued from its code and Lean's source, and observed on the worked example, not proved.
