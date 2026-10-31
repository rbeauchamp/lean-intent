# lean-intent

A Lean library for writing what an owner wants as formal properties, and for checking that those properties are adequate, before any code is written.

A proof shows that code meets its specification, never that the specification says what its owner meant. A specification that misses the owner's intent is a bug of the same standing as code that misses its specification. This library gives a Lean project, and the coding assistant working in it, the means to state what an owner wants as formal properties, to check that they are adequate before any code is written, to have the owner confirm a plain restatement of them, and to prove that the code meets them.

## The owner and the agents

The owner works at the level of intent, and that level is wherever the owner actually holds intent, not a fixed depth: for a detail an agent invented, the owner's intent is the one it serves, one level up. As with an API and its implementation, what the owner states and confirms is the deliverable's contract, the preconditions on its inputs and the facts about the world it relies on (a record's domain hypotheses), the postconditions on its outcomes and mission results (its properties) and its invariants; the specifications of internal functions are implementation details that the agents own and may change. Below the owner's intent the agents derive the specification, and they make each detail as a decision recorded with its reason, tied to the owner's intent, marked as made on the owner's behalf and never presented as the owner's own. The owner's attention goes only to confirming a plain restatement of their intent (the rendering of a record), to the forks their intent leaves open that change what they get (two independent readings that disagree on something the owner would care about are one sign of such a fork), and to one-way doors and trades of quality for cost. The method does not ask the owner to answer each consequence of a record, to confirm each domain hypothesis, or to confirm each freedom O5 leaves: the agents check each consequence against the restatement the owner confirmed, and record whether it follows from that restatement or was decided on the owner's behalf, since a consequence the owner never saw is not their confirmation. Each recorded answer shows whether it is the owner's own or a decision made on the owner's behalf through the owners' log ([`docs/owners-log.md`](docs/owners-log.md)): an answer statement names who gave it, a principal acting as owner or one acting under the delegation it names, and `LeanIntent.Trace` decides whether that delegation traces back to a declared owner. The answers a project keeps against its revisions (`LeanIntent.Answer`) name no author; `LeanIntent.Attributed` pairs each with who gave it, and `LeanIntent.Confirmation` ties that, and what a record says of who settled each thing, to the log and to the revision each applies to ([`docs/confirmation.md`](docs/confirmation.md)). A rendered record says who settled each thing, as the record holds it: confirmed by the owner, derived from what the owner confirmed, decided on the owner's behalf, left to the owner as a fork, or not settled ([who settled each thing](docs/who-settled.md)).

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

## Upgrading from `import LeanIntent`

Earlier versions had two modules, `LeanIntent` and `LeanIntentExamples`, that only imported the others (`LeanIntent` all but those of the rendering). They are removed, because a module that imports every other is a list that every feature edits. A project that writes `import LeanIntent` imports instead the modules whose declarations it uses.

A build that holds no compiled file of the removed module, such as one from a fresh clone, refuses `import LeanIntent`: Lean reports that the object file of module `LeanIntent` does not exist. A build directory made before the upgrade still holds that file, and Lake, for which `LeanIntent` is no longer a module of the package, neither rebuilds nor removes it, so Lean would go on importing it, and through it the library's modules as they were last built, with no error. So delete lean-intent's build directory when upgrading (in a project that requires it, `.lake/packages/lean-intent/.lake`) and build again.

## Adding a feature

A feature adds files of its own and edits no file that every feature shares: its modules under `LeanIntent/`, its worked examples under `LeanIntentExamples/`, and its document under `docs/`. Lake builds every Lean file under those two directories, since `lakefile.toml` selects each library's modules by a glob over its directory rather than by a list; `tools/check.lean` builds and audits every one, and refuses a library file that no library target selects; and this README lists no feature. So two features in different modules edit no line in common. A feature that builds on an existing worked example imports it from a file of its own, as `LeanIntentExamples/Answers.lean` imports the sorting records, rather than extending that example's file. A worked example shows how a record is written and used, and does not pin what a function returns for chosen inputs, which the feature's module states over every input; the exceptions are the owners' log's example text, which shows the grammar's committed format, and what a decision accepts and refuses, as in `LeanIntentExamples/Trace.lean` and `LeanIntentExamples/Confirmation.lean`, which shows what it names.

## What is trusted

- Lean, its kernel and its three axioms (`propext`, `Classical.choice`, `Quot.sound`).
- That a record's properties, domain hypotheses, vocabulary and shape say what the owner meant. This is the one link no proof reaches; the owner validates it by confirming the record's plain restatement, rendered by `LeanIntent.Render`, and deciding the forks it leaves open, and those answers, with the decisions the agents make on the owner's behalf, are kept by `LeanIntent.Answers` (whether an answer of the owners' log has authority that traces back to a declared owner is decided by `LeanIntent.Trace`, and whether a deliverable's stored answers and statuses agree with the log, and its current revision is confirmed, by `LeanIntent.Confirmation`).
- What each feature's document lists under its own What is trusted.

## Checks

`tools/check.lean` is the repository's one check program. `lean --run tools/check.lean` builds the library with warnings as errors (a `sorry` is a warning), refuses a library file that no library target of `lakefile.toml` selects and a module a target selects whose file Git's index does not list, so that it builds and audits exactly what a build of the library targets builds, refuses a `lakefile.toml` that requires another package, and audits every declaration's axioms; `lean --run tools/check.lean --tests` lists the repository's tests, which must be none. Its module comment states what each rule decides and what it does not. lean-intent has no CI: the local no-mistakes validation is its merge gate, and its Test step runs both, failing when the listing prints anything (`commands.test` in `.no-mistakes.yaml`).

## Design

The obligations are Lean propositions about the record, and the store of a record's statements is Lean's environment, in which a record, once declared, has a fixed value.
