# The adequacy obligations

**The adequacy obligations O1 to O5**, each computed from the record by a goal former whose correctness theorem is proved, so an assistant obtains each obligation from the library instead of writing a weaker one by hand: the record is well formed (O1), its hypotheses and then the whole record have a model (O2), each property can fail (O3), a subject that does nothing fails it (O4, by what doing nothing means for its shape), and any two subjects that meet it are equal or differ only in a stated freedom (O5), which is part of the restatement the owner confirms, a fork they decide when it changes what they get, or else a decision made on the owner's behalf.

Modules: `LeanIntent/Obligations.lean`, and `LeanIntent/Progress.lean` for the progress theorem. A record generic in a world's types has [a document of its own](generic-records.md).

**Complete in this version:** the five obligations with their goal formers and correctness theorems, and the progress theorem (the obligations refuse no record with content).

| Obligation | What it asks of a record `r` | Former and correctness theorem |
|---|---|---|
| O1, well formed | Every statement is a well-typed proposition. Its goal is a type: each statement paired with the type it is admitted at, which Lean's kernel checks when `r` is declared, so O1 holds by construction. | `o1`, `o1_correct`, `o1_wellTyped` |
| O2, satisfiable | At confirmation: a subject of which every domain hypothesis holds, and an instance of each vocabulary predicate. Before a deliverable runs: a subject that meets the whole record, which the deliverable supplies. | `o2`, `o2_correct`; `o2Run`, `o2Run_correct` |
| O3, refutable | Each property has a subject that fails it. | `o3`, `o3_correct` |
| O4, progress | By the subject's `Shape`: nothing of a plain value; totality of a function, which every Lean function has; for a step of a system with state, that every step leaving the state unchanged fails the record; and for a description made of functions, that its functions and plain values are the whole subject, that each function can be any function of its type, and that every subject in which one of the functions ignores its input fails the record. | `o4`, `o4_correct` |
| O5, determinate or confirmed freedom | Any two subjects that meet the record are equal (`.eq`), related by a stated relation (`.rel R`), or only both models (`.widest`), which every record meets, so O5 never refuses on its own: it makes the freedom explicit, to be confirmed with the restatement, decided by the owner where it is a fork that changes what they get, or otherwise decided on the owner's behalf. | `o5`, `o5_correct` |

Each correctness theorem equates the former's output with an intended proposition written by a direct match on the record, sharing no definition with the former or its helpers, for every record, so a former that stated `True`, a weaker proposition, or the obligation for one example only would fail it.

## O4 of a description made of functions

A subject with no state can still do nothing. A world's day rules and a pair of hash functions carry nothing from one use to the next, so no step leaves a state unchanged; what a trivial such subject does is ignore its inputs, as a pair of functions sending everything to spot 0 does. Declared a plain value (`.value`), of which O4 asks nothing, such a record passes O4 whatever it says. Declare it `Shape.bundle data first rest` instead: at least one function, each named with how a subject gives it (`Member`), and the plain values that are the rest of the subject.

O4 then asks three things (`o4`, `o4_correct`). The functions and the plain values determine the subject (`Shape.Covers`), so a function left out of the description is refused. Each function can be any function of its type (`Shape.Free`), so a decoy whose behaviour is fixed whatever the subject is, which could never ignore its input, is refused. And every subject in which any one of the functions ignores its input fails the record, not only the subject in which all of them do. What that rules in and out:

- A record with no hypothesis and no property fails O4, wherever the first function can return a value, because a subject giving a constant function exists and meets it (`not_o4_bundle_of_trivial`). The type of `Shape.bundle` requires a first function, so the list of functions cannot be empty.
- The pair of functions sending everything to spot 0 fails the hash record, which so has O4 (`LeanIntentExamples.Mixing.hashes_o4`).
- A function with at most one input always ignores it, so a record with one cannot have both O4 and a model (`no_model_of_o4_bundle_subsingleton`): a plain value goes in `data`.
- A function that may rightly be constant, such as an optional bonus that may be zero, is not one this asks about: it goes in `data` too, where the rendering shows it. Nothing proves `data` holds no function a record should ask about; that is part of the shape a record's author is trusted to declare, [as for every shape](intent-record.md#what-is-trusted).

## O2 before running, for a property over all 64-bit inputs

A property such as "no fixed rule keeps every spot", over every input of a 64-bit mixing function, cannot be evaluated: there are 2^64 differences, and a kernel computation that visits them exhausts any machine's memory long before it ends. O2 before running does not ask for that. It asks that the record has a model, and any model will do, so the recipe is to build one made for the proof, rather than to run the real function. [`LeanIntentExamples/Mixing.lean`](../LeanIntentExamples/Mixing.lean) carries it out on the hash record the Acorn pilot left without O2 before running (`hashes_o2Run`):

1. Start from a function linear in the shifts the property speaks of, such as the exclusive or of the inputs, which fails only by those shifts.
2. Break the symmetry at a few chosen words (`scramble`), differently for each input. An exchange of one pair of words commutes with exclusive or by its difference, so it takes two pairs with no common difference, and a pair that differs by input so that no reordering is a symmetry.
3. Separate the variables: a sum of functions of one input each keeps its value only if each input's own difference is constant (`separate`), so the property over all rules reduces to one statement about one input.
4. Reduce that statement to finitely many words by algebra (`rigid_flip`, `rigid_add`), and let Lean's kernel refute those at a few inputs (`table`, 288 evaluations). Nothing enumerates a 64-bit domain, and `native_decide` is not used, so the proof rests on Lean's axioms alone.

**Resource bound.** The file checks under `lean -M 1024` with two threads; observed at Lean v4.35.0, it took under a second, 463 MB resident (most of it Lean's own files, mapped) and a physical footprint of 124 MB. The cost is that of the fixed number of words the proof names, whatever the width of the words it quantifies over.

**What this establishes, and what it does not.** That the record does not contradict itself: some subject meets the whole of it. `model` is no hash function, and the theorem says nothing of a function a project runs. Whether that function meets the record is the implementation's own obligation (`IntentRecord.Fulfilled`), and in the Acorn pilot it stays open for the rules that shift two or more inputs (rbeauchamp/acorn#184).

**When the recipe does not apply.** A model must be the real function when the record determines it, as with O5 with equality over a function no simple model matches, or when the proof of a model is out of reach for another reason. Then O2 before running stays open, and a project may accept that only by saying what is established instead, in the place it records its decisions: that O2 holds at confirmation (a model of the hypotheses and an instance of each predicate), which is much less than a model of the record, so the record could still contradict itself, and every proof that an implementation fulfils it could hold vacuously where the hypotheses fail; which parts of the properties are proved of the implementation, by name; the argument that a model exists, labelled as argued and not proved; and who accepted the gap, since a gap of this kind is a trade of quality for cost, which an owner decides. Such an acceptance proves nothing and no theorem of this library stands on it: a project that accepts it has no `O2Run`.

## Worked examples

- [`LeanIntentExamples/Sorting.lean`](../LeanIntentExamples/Sorting.lean): a sorting record that forgets that the output is a rearrangement of the input fails O5, because the function returning the empty list meets it (`sortedOnly_not_o5_eq`); the corrected record meets O1 to O5, refutes that function, and is fulfilled by `List.mergeSort` through the refinement link. The degenerate check reports the empty-list function for the first record (`sortedOnly_verdicts`, `sortedOnly_possibilities`) and nothing for the corrected one (`sorting_verdicts`), which keeps the owner's declining it (`sorting_keeps_declined`). A contradictory domain hypothesis fails O2, and a property nothing fails fails O3. Both records are explained for their owner (`sortedOnlyExplained`, `sortingExplained`): shown the first, the owner declines its possibility that a function meeting it returns the empty list for every input.
- [`LeanIntentExamples/Counter.lean`](../LeanIntentExamples/Counter.lean): a counter's step that may do nothing fails O4; one that must add one meets it. Declared with the wrong shape, as a plain value, the first record meets O4, yet the degenerate check still reports the step that does nothing (`neverDecreasesAsValue_verdicts`).
- [`LeanIntentExamples/Mixing.lean`](../LeanIntentExamples/Mixing.lean): the pair of hash functions on three 64-bit words, declared `Shape.bundle`, with O2 before running by the recipe above and O4 refusing the pair of constant functions.
- [`LeanIntentExamples/DayWorld.lean`](../LeanIntentExamples/DayWorld.lean): a world's day, a description made of functions and generic in the world's types, whose O4 needs witnesses of those types; see [generic records](generic-records.md).

## What is trusted

What the obligations trust about a record's shape and its domain hypotheses is listed with [the intent record](intent-record.md#what-is-trusted).
