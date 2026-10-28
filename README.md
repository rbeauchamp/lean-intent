# lean-intent

A Lean library for writing what an owner wants as formal properties, and for checking that those properties are adequate, before any code is written.

A proof shows that code meets its specification, never that the specification says what its owner meant. A specification that misses the owner's intent is a bug of the same standing as code that misses its specification. This library gives a Lean project, and the coding assistant working in it, four things:

- **An intent record** (`LeanIntent.IntentRecord`): named properties of one deliverable's subject, over a vocabulary of predicates, under named domain hypotheses, written before the implementation exists.
- **The adequacy obligations O1 to O5**, each computed from the record by a goal former whose correctness theorem is proved, so an assistant obtains each obligation from the library instead of writing a weaker one by hand: the record is well formed (O1), its hypotheses and then the whole record have a model (O2), each property can fail (O3), a subject that does nothing fails it (O4), and any two subjects that meet it are equal or differ only in a freedom the owner confirms (O5).
- **The degenerate-subject check** (`LeanIntent.degenerate`, `LeanIntent.Verdicts`): the degenerate subjects of the record's type (each constant function, the identity, the empty output and each projection), computed from the type alone and never chosen per record; for each, a proved verdict on whether it meets the record; and each that does reported as a possibility for the owner to confirm or decline.
- **A refinement link** (`LeanIntent.Refines`, `LeanIntent.fulfils`): a proof that the code meets its specification, and a proof that the specification refines the intent record, compose into a proof that the code fulfils the intent.

**Complete in this version:** the intent record, the five obligations with their goal formers and correctness theorems, the progress theorem (the obligations refuse no record with content), the degenerate-subject check with the theorems that fix its class, the refinement link with its transfer theorems, and worked examples. Every claim the library makes about itself is a theorem Lean's kernel checks, resting only on Lean's own axioms; the repository has no tests.

**Not yet built**, each a separate issue of this repository: refusing a record that depends on its own implementation (#2), keeping every confirmed and declined consequence across revisions (#3), rendering records and their consequences for the owner (#4), recording the owner's confirmations so that only the owner can make them (#5), and extending the degenerate check to types the project declares, higher-order subjects and large finite types (#11). Until #5 lands, nothing in the library records that the owner confirmed a record or a freedom.

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
import LeanIntent
open LeanIntent

def Sorted (l : List Int) : Prop := l.Pairwise (· ≤ ·)

def sorting : IntentRecord (List Int → List Int) where
  shape := .function _ _
  dom := []
  props := [⟨"sorted", fun f => ∀ l, Sorted (f l)⟩, ⟨"rearranges", fun f => ∀ l, (f l).Perm l⟩]
  vocab := [⟨"Sorted", List Int, Sorted⟩, ⟨"Perm", List Int × List Int, fun p => p.1.Perm p.2⟩]
```

and prove its obligations: `O2 sorting`, `O2Run sorting`, `O3 sorting`, `O4 sorting` and `O5 sorting .eq`. Each `Oi r` is the conjunction of the goals its former computes (`o2 r` and the rest), and `oi_correct` turns it into the intended proposition, which is usually the easier form to prove. O1 holds of every record by construction (`o1_wellTyped`). Then state and prove the degenerate check's verdicts, `Verdicts sorting [false, false]`: neither the function returning the empty list nor the identity meets the corrected record. [`LeanIntentExamples/Sorting.lean`](LeanIntentExamples/Sorting.lean) does all of this, and then proves an implementation fulfils the record through the refinement link.

## The obligations

| Obligation | What it asks of a record `r` | Former and correctness theorem |
|---|---|---|
| O1, well formed | Every statement is a well-typed proposition. Its goal is a type: each statement paired with the type it is admitted at, which Lean's kernel checks when `r` is declared, so O1 holds by construction. | `o1`, `o1_correct`, `o1_wellTyped` |
| O2, satisfiable | At confirmation: a subject of which every domain hypothesis holds, and an instance of each vocabulary predicate. Before a deliverable runs: a subject that meets the whole record, which the deliverable supplies. | `o2`, `o2_correct`; `o2Run`, `o2Run_correct` |
| O3, refutable | Each property has a subject that fails it. | `o3`, `o3_correct` |
| O4, progress | By the subject's `Shape`: nothing of a plain value; totality of a function, which every Lean function has; and for a step of a system with state, that every step leaving the state unchanged fails the record. | `o4`, `o4_correct` |
| O5, determinate or confirmed freedom | Any two subjects that meet the record are equal (`.eq`), related by a relation the owner confirms (`.rel R`), or only both models (`.widest`), which every record meets, so O5 never refuses on its own: it makes the freedom a question for the owner. | `o5`, `o5_correct` |

Each correctness theorem equates the former's output with an intended proposition written by a direct match on the record, sharing no definition with the former or its helpers, for every record, so a former that stated `True`, a weaker proposition, or the obligation for one example only would fail it.

## The degenerate subjects

A record can have a model and still be met by a subject that does nothing useful: a sorting record that asks only for an ascending output is met by the function that returns the empty list. The degenerate check closes this with a closed class of degenerate subjects, fixed by the subject's type and never chosen per record. Here the class covers a subject of type `a₁ → … → aₙ → b`, a plain value when `n` is zero, whose argument and output types are built from `Unit`, `Bool`, `Nat`, `Int` and `String` by `List`, `Array`, `Option`, `×` and `⊕` (`LeanIntent.Ty`). Lean's instance resolution finds the type's code (`LeanIntent.Covered`); a type it finds none for, such as a structure the project declares, a dependent or higher-order function, or a type in a higher universe, is not covered, and Lean reports that it cannot synthesize `Covered`, so no verdict about it can be stated; wider coverage is #11. Because every `Covered W` carries a proof that its code stands for `W`, a code that mis-encodes its type cannot be given, and each degenerate subject is a value of `W` itself.

| Member | Which | Theorem |
|---|---|---|
| Constant functions | At every value of `b` when `b` has finitely many; otherwise, the constants being infinitely many, at the values the rule `Ty.Small` fixes: a number, string, list or array only at its empty value, the unit type and `Bool` at every value, and an option, pair or sum at each value built from its components' parts | `Sig.const_mem_of_finite`, `Sig.constants_infinite`, `Ty.mem_part_iff` |
| The empty output | The constant at `b`'s empty value, always a member | `Sig.empty_output_mem` |
| Projections | Each function returning a component of type `b` of one of its arguments: the argument itself, or a component of a pair inside it | `Sig.proj_mem` |
| The identity | The projection of a function of one argument to its own type | `Sig.identity_mem` |

`Sig.mem_degenerate_iff` states the class apart from the list that computes it, `Degenerate.apply_fn` what each member returns, and `degenerate_ne_nil` that no class is empty. `Verdicts r bs` is the check: its goals (`verdicts`) state, for each degenerate subject in order, that it meets `r` where `bs` says `true` and that it does not where `bs` says `false`, so every verdict is part of a theorem's statement and proved, and a list of the wrong length is refused (`verdicts_correct`). `metBy W bs` lists the subjects the verdicts report as meeting the record, exactly those that do (`mem_metBy`), and `possibilities` reports each as a `Possibility`, a consequence that shows the owner a model of the record, for the owner to confirm or decline.

## Worked examples

- [`LeanIntentExamples/Sorting.lean`](LeanIntentExamples/Sorting.lean): a sorting record that forgets that the output is a rearrangement of the input fails O5, because the function returning the empty list meets it (`sortedOnly_not_o5_eq`); the corrected record meets O1 to O5, refutes that function, and is fulfilled by `List.mergeSort` through the refinement link. The degenerate check reports the empty-list function for the first record (`sortedOnly_verdicts`, `sortedOnly_possibilities`) and nothing for the corrected one (`sorting_verdicts`). A contradictory domain hypothesis fails O2, and a property nothing fails fails O3.
- [`LeanIntentExamples/Counter.lean`](LeanIntentExamples/Counter.lean): a counter's step that may do nothing fails O4; one that must add one meets it. Declared with the wrong shape, as a plain value, the first record meets O4, yet the degenerate check still reports the step that does nothing (`neverDecreasesAsValue_verdicts`).
- [`LeanIntentExamples/Decision.lean`](LeanIntentExamples/Decision.lean): a procedure deciding evenness, `Nat → Bool`, whose output type has finitely many values, so the degenerate class holds the constant function at each; a record asking only for sound answers is met by the procedure that always answers `false`, which the check reports.
- [`LeanIntentExamples/Transfer.lean`](LeanIntentExamples/Transfer.lean): a refinement link carries the record's guarantees to the mapping's image, not to the implementations themselves.

## What is trusted

- Lean, its kernel and its three axioms (`propext`, `Classical.choice`, `Quot.sound`).
- That a record's properties, domain hypotheses, vocabulary and shape say what the owner meant. This is the one link no proof reaches; the owner validates it by confirming the record's consequences in plain words (#4, #5).
- That a record's shape is the one its subject has: a subject with state declared as a plain value is asked nothing by O4. The degenerate check, fixed by the subject's type rather than its declared shape, narrows this. For a covered step without output (`S → S`, `S → I → S`) the step that does nothing is a projection, so a record it meets reports it to the owner, though it does not refuse the record as O4 would. A step with output (`S → O × S`, `S → I → O × S`) does nothing by returning any output with the state unchanged. The class does not generally enumerate these state-preserving subjects, although some coincide with its constants or projections: for `Unit → Bool × Unit`, every constant preserves the state and is in the class. The shape therefore stays trusted.
- That the domain hypotheses are true of the world, which the owner confirms; a hypothesis that excludes the subject that does nothing, or all but one model, would make O4 or O5 hold vacuously, and one that excludes a degenerate subject keeps the degenerate check from reporting it.
- That a covered type has only the code the library's instances find for it, so that no record can be checked against a smaller class: another instance would have to prove its code's type equal to the type, and for two different codes that equates two different types, which Lean cannot prove without a further axiom. This is argued, not proved.
- That a constant function the class leaves out is not one the owner needed to see: where the output type has infinitely many values the class takes only the constants its rule fixes, so a record met by the function returning `[0]` for every input, and by no member, is not reported. No finite set of checked subjects closes this gap for every record; the freedom O5 shows the owner still spans it.
- That every record about a covered type has its verdicts stated, and every record about another type is checked by other means: Lean refuses to state verdicts about a type the class does not cover, but nothing in the library requires verdicts of a record, as nothing requires O1 to O5.
- That a record was written before its implementation was read, and does not depend on it (#2).

## Checks

`tools/check.lean` is the repository's one check program. `lean --run tools/check.lean` builds the library with warnings as errors (a `sorry` is a warning), refuses a `lakefile.toml` that requires another package, and audits every declaration's axioms; `lean --run tools/check.lean --tests` lists the repository's tests, which must be none. Its module comment states what each rule decides and what it does not. lean-intent has no CI: the local no-mistakes validation is its merge gate, and its Test step runs both, failing when the listing prints anything (`commands.test` in `.no-mistakes.yaml`).

## Design

The obligations are Lean propositions about the record, and the store of statements is Lean's environment, in which a record, once declared, has a fixed value.
