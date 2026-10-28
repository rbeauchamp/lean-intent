# lean-intent

A Lean library for writing what an owner wants as formal properties, and for checking that those properties are adequate, before any code is written.

A proof shows that code meets its specification, never that the specification says what its owner meant. A specification that misses the owner's intent is a bug of the same standing as code that misses its specification. This library gives a Lean project, and the coding assistant working in it, three things:

- **An intent record** (`LeanIntent.IntentRecord`): named properties of one deliverable's subject, over a vocabulary of predicates, under named domain hypotheses, written before the implementation exists.
- **The adequacy obligations O1 to O5**, each computed from the record by a goal former whose correctness theorem is proved, so an assistant obtains each obligation from the library instead of writing a weaker one by hand: the record is well formed (O1), its hypotheses and then the whole record have a model (O2), each property can fail (O3), a subject that does nothing fails it (O4), and any two subjects that meet it are equal or differ only in a freedom the owner confirms (O5).
- **A refinement link** (`LeanIntent.Refines`, `LeanIntent.fulfils`): a proof that the code meets its specification, and a proof that the specification refines the intent record, compose into a proof that the code fulfils the intent.

**Complete in this version:** the intent record, the five obligations with their goal formers and correctness theorems, the progress theorem (the obligations refuse no record with content), the refinement link with its transfer theorems, and worked examples. Every claim the library makes about itself is a theorem Lean's kernel checks, resting only on Lean's own axioms; the repository has no tests.

**Not yet built**, each a separate issue of this repository: refusing a record that depends on its own implementation (#2), keeping every confirmed and declined consequence across revisions (#3), rendering records and their consequences for the owner (#4), recording the owner's confirmations so that only the owner can make them (#5), and checking every specification against the degenerate implementations of its type (#6). Until #5 lands, nothing in the library records that the owner confirmed a record or a freedom.

## Using it

The library depends on nothing beyond Lean's own libraries, and builds on the Lean release `lean-toolchain` names (`v4.34.1`). Add it to a Lake project's `lakefile.toml`:

```toml
[[require]]
name = "lean-intent"
git = "https://github.com/rbeauchamp/lean-intent"
rev = "main"
```

Then write the intent record for one function, before its code:

```lean
import LeanIntent
open LeanIntent

def Sorted (l : List Int) : Prop := l.Pairwise (· ≤ ·)

def sorting : IntentRecord (List Int → List Int) where
  shape := .function _ _
  dom := []
  props := [⟨"sorted", fun f => ∀ l, Sorted (f l)⟩, ⟨"rearranges", fun f => ∀ l, (f l).Perm l⟩]
  vocab := [⟨"Sorted", List Int, Sorted⟩, ⟨"Perm", List Int × List Int, fun p => p.1.Perm p.2⟩]
```

and prove its obligations: `O2 sorting`, `O2Run sorting`, `O3 sorting`, `O4 sorting` and `O5 sorting .eq`. Each `Oi r` is the conjunction of the goals its former computes (`o2 r` and the rest), and `oi_correct` turns it into the intended proposition, which is usually the easier form to prove. O1 holds of every record by construction (`o1_wellTyped`). [`LeanIntentExamples/Sorting.lean`](LeanIntentExamples/Sorting.lean) does all of this, and then proves an implementation fulfils the record through the refinement link.

## The obligations

| Obligation | What it asks of a record `r` | Former and correctness theorem |
|---|---|---|
| O1, well formed | Every statement is a well-typed proposition. Its goal is a type: each statement paired with the type it is admitted at, which Lean's kernel checks when `r` is declared, so O1 holds by construction. | `o1`, `o1_correct`, `o1_wellTyped` |
| O2, satisfiable | At confirmation: a subject of which every domain hypothesis holds, and an instance of each vocabulary predicate. Before a deliverable runs: a subject that meets the whole record, which the deliverable supplies. | `o2`, `o2_correct`; `o2Run`, `o2Run_correct` |
| O3, refutable | Each property has a subject that fails it. | `o3`, `o3_correct` |
| O4, progress | By the subject's `Shape`: nothing of a plain value; totality of a function, which every Lean function has; and for a step of a system with state, that every step leaving the state unchanged fails the record. | `o4`, `o4_correct` |
| O5, determinate or confirmed freedom | Any two subjects that meet the record are equal (`.eq`), related by a relation the owner confirms (`.rel R`), or only both models (`.widest`), which every record meets, so O5 never refuses on its own: it makes the freedom a question for the owner. | `o5`, `o5_correct` |

Each correctness theorem equates the former's output with an intended proposition written by a direct match on the record, sharing no definition with the former or its helpers, for every record, so a former that stated `True`, a weaker proposition, or the obligation for one example only would fail it.

## Worked examples

- [`LeanIntentExamples/Sorting.lean`](LeanIntentExamples/Sorting.lean): a sorting record that forgets that the output is a rearrangement of the input fails O5, because the function returning the empty list meets it (`sortedOnly_not_o5_eq`); the corrected record meets O1 to O5, refutes that function, and is fulfilled by `List.mergeSort` through the refinement link. A contradictory domain hypothesis fails O2, and a property nothing fails fails O3.
- [`LeanIntentExamples/Counter.lean`](LeanIntentExamples/Counter.lean): a counter's step that may do nothing fails O4; one that must add one meets it.
- [`LeanIntentExamples/Transfer.lean`](LeanIntentExamples/Transfer.lean): a refinement link carries the record's guarantees to the mapping's image, not to the implementations themselves.

## What is trusted

- Lean, its kernel and its three axioms (`propext`, `Classical.choice`, `Quot.sound`).
- That a record's properties, domain hypotheses, vocabulary and shape say what the owner meant. This is the one link no proof reaches; the owner validates it by confirming the record's consequences in plain words (#4, #5).
- That a record's shape is the one its subject has: a subject with state declared as a plain value is asked nothing by O4. The degenerate-implementation check (#6), whose subjects are fixed by the subject's type, is to close this.
- That the domain hypotheses are true of the world, which the owner confirms; a hypothesis that excludes the subject that does nothing, or all but one model, would make O4 or O5 hold vacuously.
- That a record was written before its implementation was read, and does not depend on it (#2).

## Checks

`tools/check.lean` is the repository's one check program. `lean --run tools/check.lean` builds the library with warnings as errors (a `sorry` is a warning), refuses a `lakefile.toml` that requires another package, and audits every declaration's axioms; `lean --run tools/check.lean --tests` lists the repository's tests, which must be none. Its module comment states what each rule decides and what it does not. lean-intent has no CI: the local no-mistakes validation is its merge gate, and its Test step runs both, failing when the listing prints anything (`commands.test` in `.no-mistakes.yaml`).

## Origin

This library ports the intent-and-specification layer that loam designed in its record 0026 and built in part (loam #241 and #242). Loam states the obligations about terms of its own kernel, read in a set model; here they are Lean propositions, and the store of statements is Lean's environment.
