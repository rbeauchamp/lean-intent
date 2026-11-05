# The implementation of a deliverable

**The implementation of a deliverable** (`LeanIntent.Implementation`, `LeanIntent.AwaitingImplementation`, `LeanIntent.Implementation.Read`): a value a project declares that names the constant implementing a deliverable, by its module and its name as Lean's environment gives them, together with the proof that it fulfils the deliverable's record, so that the fulfilment a gate reads is of that constant and of no other; a value that declares, with its reason, that a deliverable awaits its implementation, for the time between the owner's confirmation of its record and the implementation's proof; and the decision a project's gate runs on those values, read from the finished build, with theorems stating what it decides.

Modules: `LeanIntent/Implementation.lean` (the value, the decision and its theorems, which import no more of Lean than the rest of the core) and `LeanIntent/Implementation/Read.lean` (reading the build, which imports all of Lean).

**Complete in this version:** the value, the declaration that a deliverable awaits its implementation, the decision with its theorems, and the reader a gate calls. That the recorded constant is what a program runs is not established; see [What is trusted](#what-is-trusted).

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

## A deliverable awaiting its implementation

The owner confirms a deliverable's record before any implementation exists, so for a while a declared and confirmed deliverable is deliberately unimplemented. Until its implementation is proved, the project declares that state, in a module that imports the deliverable and that the gate reads:

```lean
import LeanIntent.Implementation

/-- The sorting deliverable awaits its implementation. -/
def sortingAwaiting : LeanIntent.AwaitingImplementation sortingDeliverable where
  reason := "The owner has confirmed the record; its program is not written yet."
```

The reason says why the implementation is awaited or where its work is tracked, such as the address of an issue. It cannot be blank: the structure's field `stated` holds the proof that the reason has a character that is not whitespace, which its default, `decide +kernel`, has Lean's kernel decide, so a blank reason is refused when the value is declared and is no value of the type (`blank_unrepresentable` in the worked example). The reader reads the reason as the kernel reduces it to a string literal, so write it as a literal or as a constant whose value is one; a reason computed by a function, such as `"tracked in " ++ url`, is accepted by the type but is an error of the reader naming the value.

The decision accepts a deliverable with exactly one such value and no implementation as it accepts one with exactly one implementation and no such value, and lists it in the report with the value and the reason, so a gate can print what is still awaited and why.

To retire the state once the implementation exists and its proof is done, the project deletes the value and declares the deliverable's `Implementation` value in the same change. Nothing else changes: the deliverable, its explanation, its answers and the owners' log stay as they were confirmed, and `Implementation.replace_nil_iff` states that the decision's verdict with the implementation in place of the declaration is the one it had with the declaration. Leaving the declaration beside the implementation is refused, naming the declaration (`awaitingImplemented`), so a declaration left unretired fails a gate that reads both values' modules.

## What the type establishes

The field `fulfils` has the type `d.record.Fulfilled subject`. Lean's kernel checks every declaration: it refuses a definition whose value's type is not definitionally equal to its declared type (`environment::add_definition`, `src/kernel/environment.cpp` of Lean v4.35.0), and an application whose argument's type is not definitionally equal to its binder's, with the arguments before it substituted (`type_checker::infer_app`, `src/kernel/type_checker.cpp`, lines 173 to 187). So a value's proof proves that the record is fulfilled by the very subject the value records.

- A theorem that another constant fulfils the record is accepted as the proof only where the two constants are definitionally equal, as for an alias `def sortAlias := sortProgram`; the proposition is then the same one, and what it proves is that the recorded constant fulfils the record.
- A theorem about a constant that differs, such as a wrapper that returns `[]` for long lists, is refused: Lean reports a type mismatch (written with `where` or `{ … }`) or an application type mismatch (written `⟨…⟩` or `Implementation.mk …`), naming the proof, the proposition it proves and the one expected, and the project does not build. This was observed at Lean v4.35.0.
- So a subject can be recorded as the implementation exactly when it fulfils the record (`Implementation.exists_iff`), and the function returning the empty list, which fails the sorting record, cannot be recorded by any proof (`nilSort_unrecordable` in the worked example).
- A theorem elsewhere in the project about another constant, such as `sorting.Fulfilled List.mergeSort`, is no value of this type, and the decision does not read it.

## How it ties to the owners' log, and what it leaves unchanged

A value of `Implementation d`, or of `AwaitingImplementation d`, names its deliverable in its type, the deliverable names its record, and the answers of the project's owners' log name that record and the text of its revision ([the confirmation check](confirmation.md#what-it-decides)). Nothing of the value enters the texts an answer holds: they are computed from the deliverable's explanation and what its meaning reaches (`Render.revisionText`, `Render.consequenceText`), and the value is declared after the deliverable its type names, so nothing the deliverable holds refers to it, since a declaration refers only to constants the environment already holds (`environment::get`, which the kernel's `type_checker::infer_constant` calls, refuses an unknown constant). Recording the implementation, declaring that the deliverable awaits one, replacing either value with the other or with another of its kind, or moving a value to another module therefore changes no answer's text, and the confirmations stand; the confirmation check finds no value of either type, so its report is unchanged too. This was observed at Lean v4.35.0 on the worked examples: with the awaiting value's module read as with the implementation's, the confirmation reader's revision text of the sorting deliverable was byte for byte the same, and the confirmation check found the same number of findings.

Renaming a constant changes the text of every revision and answer whose meaning reaches it, as it always has. A record's meaning reaches no declaration of its implementation where [cone exclusion](cone-exclusion.md) accepts it, and a gate can pass the recorded constant to `LeanIntent.Cone.checkRecord` as the implementation. A consequence the explanation shows may still name a function: in the worked example the explanation reaches `sort`, through the consequence the assistant answered, and never `sortProgram`, the implementation recorded.

## What it decides

The decision (`Implementation.findings`) reads, for each value a project declares, the deliverable its type names and either the constant its subject is (`Implementation.Entry`) or the reason it gives for awaiting one (`Implementation.AwaitingEntry`), and lists what is wrong:

- **No deliverable** (`noDeliverable`): a project that declares none has nothing implemented, never a pass.
- **A deliverable no value implements and none declares awaiting its implementation** (`unimplemented`), naming it: nothing then says which code fulfils it, or that none is meant to yet.
- **A deliverable several values implement** (`several`), naming it and them, whichever constants they record: the project's declarations would then not tell which program is the deliverable's.
- **A value tied to no deliverable** (`untied`), naming it: its type names a deliverable the modules read do not declare, or a term in place of a deliverable's constant.
- **A value whose subject is not a constant** (`notConstant`), naming it: a term such as `fun l => sort l` names no constant a reader can find.
- **A deliverable several values declare awaiting its implementation** (`severalAwaiting`), naming it and them.
- **A deliverable with an implementation that values still declare awaiting one** (`awaitingImplemented`), naming it and those values: the declaration was not retired, and now says something false.
- **A declaration of an awaited implementation tied to no deliverable** (`untiedAwaiting`), naming it, as for an implementation.

| Theorem | What it establishes |
|---|---|
| `findings_eq_nil_iff` | for every list of deliverables and of entries of both kinds, the decision finds nothing exactly when there is a deliverable; each has exactly one entry recording its implementation and none declaring it awaited, or none recording its implementation and exactly one declaring it awaited; each entry names one of them; and each implementation records a constant (`Accounted`, stated with counts over the lists and sharing no definition with the decision) |
| `findings_sound` | each finding holds of the deliverables and entries, and names the deliverable or the value it is about |
| `mem_implementations` | the report lists a deliverable with a value and a constant exactly when that value is the one entry recording its implementation, and that constant its subject |
| `mem_awaiting` | the report lists a deliverable with a value and a reason exactly when that value is the one entry declaring it awaited, and that reason the one it gives |
| `listed_of_nil` | where the decision finds nothing, the report lists every deliverable, either with its value and the constant, by module and name, no value declaring it awaited, or with the value declaring it awaited and its reason, no value recording an implementation |
| `replace_nil_iff` | replacing an entry that declares a deliverable awaited with an entry recording that deliverable's implementation, which records a constant, leaves the decision's verdict as it was |
| `AwaitingImplementation.stated` | the reason a value declaring an awaited implementation gives is not blank |
| `Implementation.fulfilled`, `Implementation.exists_iff`, `Implementation.meets` | a value's subject fulfils the record; a subject can be recorded exactly when it fulfils it; and it meets the record wherever the domain hypotheses hold of it |

The decisions, each made on the owner's behalf, which a later change can reverse:

- **One implementation for each deliverable, or one declaration that it awaits one, and not both.** A project with two programs for one record declares two deliverables, each with its own value. A declaration left beside the implementation is refused rather than ignored, since it would say of the project something no longer true.
- **The awaited state is a value the project declares, with its reason, not a list the gate keeps.** It is read from Lean's environment as an implementation is, ties to the deliverable through its type, and is retired in the same change that records the implementation.
- **A reason is required and is not blank, by its type; the decision does not read it.** The report gives it, for a gate to print.
- **One constant may implement several deliverables.** Each value's proof is of its own deliverable's record, so a theorem about one record discharges no other, and one program may be what two contracts are about (`oneConstant_accepted`).
- **The subject is a constant, and nothing else.** The decision accepts this closed form and refuses every other by name, rather than reading a term's head or unfolding it, since a term could hold the implementation under any wrapper.
- **The module is read, not written.** Lean's environment records the one module that declares each constant, so the report gives the module and the name of the constant the value holds, and no field written by hand could disagree with it.

## What a gate reads

`LeanIntent.Implementation.Read.check mods`, given the project's modules as Lake lists them, the same list given to `LeanIntent.Confirmation.Read.check`, reads everything from Lean's environment and parses no source text, as its module comment's table states for each input: the deliverables as the confirmation check finds them, every constant whose type reduces to `Implementation _`, the deliverable its type names, the subject of its value reduced by `Render.readWhnf` to the constructor's application, and the module the environment records for that constant (`Environment.getModuleIdxFor?`); and every constant whose type reduces to `AwaitingImplementation _`, the deliverable its type names, and the reason of its value reduced by `Render.readWhnf` to the constructor's application, which the kernel must reduce to a string literal. Discovery and constructor extraction use `Kernel.whnf`, which unfolds actual declarations and leaves a constructor's arguments as they are (`type_checker::whnf_core`, `unfold_definition` and `whnf` in Lean v4.35.0's [kernel source](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/kernel/type_checker.cpp)); it consults no elaborator unfolding helper. It returns a `Report`:

| Field | What it holds |
|---|---|
| `findings` | what is wrong; empty exactly when every deliverable is accounted for as above, implemented or declared awaiting its implementation |
| `implementations` | each deliverable implemented by exactly one value whose subject is a constant, with that value and the constant's module and name |
| `awaiting` | each deliverable that exactly one value declares awaiting its implementation, with that value and the reason it gives |

A value of either kind that is an opaque constant or an axiom, which does not reduce to its constructor's application, is an error naming it, never a pass, and so is every unsafe or partial constant of the types the reader looks for, `AwaitingImplementation _` among them, since it is found through the same discovery, `Confirmation.Read.declaredIn`. Every discovered definition must have safety `safe` (`Confirmation.Read.proofSafe_iff`): unsafe and partial definitions may refer to themselves and so prove anything, while a safe declaration cannot refer to either. A gate runs both checks on the same build:

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
  for (d, value, reason) in implemented.awaiting do
    logInfo m!"{d} awaits its implementation ({value}): {reason}"
```

## Why the reader requires safe definitions

The mission property is that the proof in a discovered value binds its recorded implementation to its deliverable's record. Relying on kernel checking alone missed a boundary: Lean permits recursive unsafe definitions and mutual partial definitions. A partial mutual block can contain `p : False := p` and a value whose fulfilment proof is `False.elim p`, with no additional axiom or skipped kernel check. The reader reduces the value to its constructor without inspecting that proof. Its former `ConstantInfo.isUnsafe` guard rejected only `unsafe`, leaving `partial` admitted; treating the complement of one unsafe mode as proof safety was the specification error behind the guard.

The shared discovery boundary, `Confirmation.Read.declaredWhere`, now uses `proofSafe` before adding any matching constant to its result. `proofSafe_iff` characterizes that executable predicate for every `ConstantInfo`: definitions pass exactly when their safety is `safe`, and other kinds retain their unsafe flag check. Its proof splits Lean's closed `DefinitionSafety` type into all three constructors, so both refusal of unsafe and partial definitions and admission of safe definitions are machine checked. This changes the reasoning link from an assumed meaning of `isUnsafe` to a checked positive safety contract. The same boundary serves both readers and every type they discover; it does not depend on the constant's name, body or the example that exposed the defect.

The enforcement rung for declaration admission is an invariant-derived guard with a universal characterization proved by exhaustive constructor cases. Lean's environment type permits declarations of every safety, so a type that assumed the entire input environment safe would exclude inputs the reader must diagnose. The scan's use of the predicate is argued from its code; the theorem proves the predicate, not the whole metaprogram. The kernel's exclusion of unsafe and partial references from safe declarations is read from Lean v4.35.0's [constant checker](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/kernel/type_checker.cpp); its [mutual-declaration checker](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/kernel/environment.cpp) explains why checking a partial block alone is insufficient.

Admission alone does not authenticate reduction. The former reader used `Meta.whnf`, whose default smart unfolding can replace an application of a safe definition `helper` by the body of `helper._sunfold`, without checking that auxiliary's safety or correspondence to `helper` (`Meta.unfoldDefinition?` in Lean v4.35.0's [elaborator reducer](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/Lean/Meta/WHNF.lean)). A safe value `v := helper 0` could therefore be read through an unsafe auxiliary returning another subject and a self-referential proof. Discovery skips the auxiliary's function type, and `proofSafe_iff` authenticates only `v`, not that substitution. This bypass follows from the source; it is not an executed probe. The reasoning error was treating an elaborator reduction as the kernel's reduction of an admitted declaration.

The shared reader now removes that substitution path: `Render.readWhnf` calls `Kernel.whnf` through `Render.kernelReduction`, for discovery types, implementation types and values, and every constructor, list, literal and status the confirmation reader and rendering consume. Recursive reductions are the kernel's too, so an auxiliary consulted only by the elaborator cannot enter at a nested reduction. Kernel reduction follows the admitted definitions; under kernel type preservation, a constructor extracted from a safe declared value has its declared type, and its dependent proof field belongs to the subject extracted with it. No theorem about the list-level decision establishes this external semantic property.

The reduction invariant reaches the type and construction rungs: `kernelReduction` returns an expression only with a proof that the exact request `Kernel.whnf env lctx e` returned it, and `kernelReduction_result` proves universally that erasing this proof preserves every kernel success and error. The request is stated independently of the wrapper's success. These claims establish transport, not correctness of the external kernel algorithm; the [kernel API](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/Lean/Environment.lean) exposes that algorithm as an opaque external function. There is no additional refusal when the kernel returns a result, and no fallback when it fails. The supported inputs are kernel-ready declarations and terms in the supplied local context; opaque values and axioms still fail constructor reading. This closes the reader's dependence on unchecked auxiliary reductions by construction, with no new guard or claimed proof of Lean itself. Kernel checking and reduction, accepted axioms, complete module discovery and the remaining reader correspondence are the trusted boundaries below.

## Worked examples

- [`LeanIntentExamples/Awaiting.lean`](../LeanIntentExamples/Awaiting.lean): the sorting deliverable before its implementation exists, declared awaiting it with a reason (`sortingAwaiting`); a blank reason cannot be declared (`blank_unrepresentable`); and the decision, given what the build shows, finds nothing and lists the deliverable with the value and its reason, and refuses by name an implementation recorded while the declaration stays, a second declaration, and a declaration tied to a deliverable the project does not declare or to a term; replacing the declaration with the implementation's value leaves it finding nothing (`retired`, by `replace_nil_iff`).
- [`LeanIntentExamples/Implementation.lean`](../LeanIntentExamples/Implementation.lean): the sorting deliverable of [the confirmation check's example](confirmation.md#worked-examples), implemented by a program written after its record was confirmed (`sortingImplementation`), whose proof is `sort`'s since the two are the same function by definition; the empty-list function cannot be recorded (`nilSort_unrecordable`); and the decision, given what the build shows, finds nothing and lists the program by its module and its name, and refuses by name no value, no deliverable, a second value, a value tied to a deliverable the project does not declare or to a term, and a subject that is a term, while accepting one constant that implements two deliverables. A worked example holds no build, so the reader is not run by it; it was observed at Lean v4.35.0 on the worked example and on values written to attack it, reading the program by its module and its name, refusing a second value, a term as the subject and a term as the deliverable, and giving an error on an axiom and on unsafe values. That observation was of the reader as first written, which reduced through `Meta.whnf` and refused only `unsafe` definitions; the reader as it now is, through `Render.readWhnf` and `proofSafe`, has not been run on those attacks. It was observed at Lean v4.35.0 on the worked examples and on values declaring an awaited implementation written to attack it: with the deliverable and the awaiting value it found nothing and listed the deliverable with the value and its reason; with the deliverable and the implementation it found nothing and listed the program by its module and its name; with both values it refused the declaration (`awaitingImplemented`); with neither module read it refused the deliverable as unimplemented; it refused two declarations of one deliverable and one whose type names a term; and it gave an error on an unsafe value, on a definition added with safety `partial`, on an opaque constant, on an axiom, and on a reason computed by `++`. Lean itself refuses a `partial def` of this type, which is not a function.

## What is trusted

- That the recorded constant is what a program runs. The value says which constant the project's deliverable is, and its proof binds that constant; that an executable's entry point calls it, and that its compiled code computes its definition, which `implemented_by` and `extern` replace with other code, are not established here. Accepted: a project's review reads which constant it records, and the history shows a change of it.
- That every declaration the reader reads was checked by Lean's kernel. The option `debug.skipKernelTC`, and a metaprogram that adds a declaration without checking it (`Kernel.Environment.addDeclWithoutChecking`), skip that check, so a value's proof could then prove nothing. A gate that must not trust this replays the build's declarations through the kernel.
- That a value's proof rests only on axioms the project accepts. Lean's kernel checks the proof relative to the axioms the environment declares, and `sorry` is one (`sorryAx`), which a build with warnings as errors refuses; `#print axioms` lists a value's, and the decision does not, as the confirmation check does not list those of the proofs a deliverable holds. A project's gate audits them as it audits its other proofs.
- That the modules given to `Read.check` are all the project's: a value in a module left out records nothing, so its deliverable is refused as unimplemented unless a module given declares it awaited, and a deliverable in it is not asked about. So an implementation in a module left out, beside a declaration that its deliverable awaits one in a module given, is not found, and the declaration that should have been retired passes. A constant whose type is not `Implementation _` or `AwaitingImplementation _` once every definition is unfolded, such as a function returning a value of one or a structure holding one, is not found, so it records nothing.
- That the reason a value declaring an awaited implementation gives is not blank, where its declaration skipped Lean's kernel check, as above. The decision does not read the reason, so this bears only on what the report prints.
- That Lean's kernel reduction preserves the type and meaning of the admitted declaration, and that its external implementation implements `Kernel.whnf`. The result's link to that exact request is typed, and preservation of both successes and errors is proved by `Render.kernelReduction_result`; the external algorithm is trusted with Lean. The remaining extraction of constructor arguments and names from those results, and their assembly into report inputs, is argued from the reader's code, not proved end to end.
