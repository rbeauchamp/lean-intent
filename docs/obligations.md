# The adequacy obligations

**The adequacy obligations O1 to O5**, each computed from the record by a goal former whose correctness theorem is proved, so an assistant obtains each obligation from the library instead of writing a weaker one by hand: the record is well formed (O1), its hypotheses and then the whole record have a model (O2), each property can fail (O3), a subject that does nothing fails it (O4), and any two subjects that meet it are equal or differ only in a stated freedom (O5), which is part of the restatement the owner confirms, a fork they decide when it changes what they get, or else a decision made on the owner's behalf.

Modules: `LeanIntent/Obligations.lean`, and `LeanIntent/Progress.lean` for the progress theorem.

**Complete in this version:** the five obligations with their goal formers and correctness theorems, and the progress theorem (the obligations refuse no record with content).

| Obligation | What it asks of a record `r` | Former and correctness theorem |
|---|---|---|
| O1, well formed | Every statement is a well-typed proposition. Its goal is a type: each statement paired with the type it is admitted at, which Lean's kernel checks when `r` is declared, so O1 holds by construction. | `o1`, `o1_correct`, `o1_wellTyped` |
| O2, satisfiable | At confirmation: a subject of which every domain hypothesis holds, and an instance of each vocabulary predicate. Before a deliverable runs: a subject that meets the whole record, which the deliverable supplies. | `o2`, `o2_correct`; `o2Run`, `o2Run_correct` |
| O3, refutable | Each property has a subject that fails it. | `o3`, `o3_correct` |
| O4, progress | By the subject's `Shape`: nothing of a plain value; totality of a function, which every Lean function has; and for a step of a system with state, that every step leaving the state unchanged fails the record. | `o4`, `o4_correct` |
| O5, determinate or confirmed freedom | Any two subjects that meet the record are equal (`.eq`), related by a stated relation (`.rel R`), or only both models (`.widest`), which every record meets, so O5 never refuses on its own: it makes the freedom explicit, to be confirmed with the restatement, decided by the owner where it is a fork that changes what they get, or otherwise decided on the owner's behalf. | `o5`, `o5_correct` |

Each correctness theorem equates the former's output with an intended proposition written by a direct match on the record, sharing no definition with the former or its helpers, for every record, so a former that stated `True`, a weaker proposition, or the obligation for one example only would fail it.

## Worked examples

- [`LeanIntentExamples/Sorting.lean`](../LeanIntentExamples/Sorting.lean): a sorting record that forgets that the output is a rearrangement of the input fails O5, because the function returning the empty list meets it (`sortedOnly_not_o5_eq`); the corrected record meets O1 to O5, refutes that function, and is fulfilled by `List.mergeSort` through the refinement link. The degenerate check reports the empty-list function for the first record (`sortedOnly_verdicts`, `sortedOnly_possibilities`) and nothing for the corrected one (`sorting_verdicts`), which keeps the owner's declining it (`sorting_keeps_declined`). A contradictory domain hypothesis fails O2, and a property nothing fails fails O3. Both records are explained for their owner (`sortedOnlyExplained`, `sortingExplained`): shown the first, the owner declines its possibility that a function meeting it returns the empty list for every input.
- [`LeanIntentExamples/Counter.lean`](../LeanIntentExamples/Counter.lean): a counter's step that may do nothing fails O4; one that must add one meets it. Declared with the wrong shape, as a plain value, the first record meets O4, yet the degenerate check still reports the step that does nothing (`neverDecreasesAsValue_verdicts`).

## What is trusted

What the obligations trust about a record's shape and its domain hypotheses is listed with [the intent record](intent-record.md#what-is-trusted).
