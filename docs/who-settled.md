# Who settled each thing

**Who settled each thing** (`LeanIntent.Settled`): what a project records about who confirmed or answered something, and the only words the rendering prints about it, each a function of that record, so a reader of a rendered record is never told the owner confirmed what they never saw.

Module: `LeanIntent/Settled.lean`, read and printed by `LeanIntent/Render.lean`.

**Complete in this version:** the record of who settled each thing, its printed words and the theorems that say what they claim, and the rendering and the answer's text printed through them.

**Not yet built**, a separate issue of this repository: checking what is recorded here against the owners' log, and against the revision each applies to (#5).

The owner states and confirms a system's contract, and the agents decide what lies below it on the owner's behalf, as [the README](../README.md#the-owner-and-the-agents) sets out. So each thing a rendered record shows says who settled it:

| Recorded | Printed, opening with |
|---|---|
| `Restatement.confirmed o` | `Confirmed by the owner o.` |
| `Restatement.unconfirmed` | `No confirmation by an owner is recorded.` |
| `Settled.answered (.owner p) .confirmed` | `Confirmed by the owner p.` |
| `Settled.answered (.owner p) .declined` | `Declined by the owner p.` |
| `Settled.answered (.onBehalf p d why) .confirmed` | `Confirmed on the owner's behalf by p, under the delegation d, for this reason: why` |
| `Settled.answered (.onBehalf p d why) .declined` | `Declined on the owner's behalf by p, under the delegation d, for this reason: why` |
| `Settled.derived` | `Derived from what the owner confirmed:` and which owner confirmed the restatement |
| `Settled.fork` | `A fork for the owner to decide:` |
| `Settled.unsettled` | `Not settled:` |

A consequence is one of these and no other, and an explanation (`LeanIntent.Explanation`) must give each of its consequences a status, and itself a `Restatement`: there is no default. `Settled` is indexed by the restatement's standing, and `.derived` exists only at `.confirmed o`, so a consequence of a record with no recorded confirmation cannot be recorded as derived from one: Lean's elaborator refuses it. An answer printed alone is an `Attributed`, an answer with its `Answerer`; `Answerer` has one constructor for the owner and one for a principal under a named delegation, which must give a reason, and `Authority.answerer` reads it from an authority of [the owners' log](owners-log.md).

| Theorem | What it establishes, for every status `x` |
|---|---|
| `Settled.says_iff` | the printed words start with a claim's phrase exactly when the status makes that claim, whatever names and reason it holds |
| `Settled.says_confirmed_by_owner_iff`, `Settled.says_declined_by_owner_iff` | the words say the owner confirmed, or declined, exactly when the owner is the recorded answerer with that verdict |
| `Settled.says_on_behalf_iff` | the words say an answer was given on the owner's behalf exactly when a principal under a delegation is the recorded answerer |
| `Settled.onBehalf_not_owners` | an answer given on the owner's behalf is never printed as the owner's, even with a reason that claims it was |
| `Settled.says_derived_confirmed` | the words say a consequence is derived only of a record whose restatement stands as confirmed |
| `Restatement.says_confirmed_iff` | the words say the restatement is confirmed exactly when that is recorded |

So a record with no answers and no confirmation prints neither, and a record whose answers come from a mix of owner and delegates prints each as the one who gave it.

A fork is the one consequence the rendering puts to the owner, since their attention goes to forks their intent does not settle; every other unanswered consequence says only that it is not settled, or derived. A derived consequence is proved of the record (`Shown.holds`), and a possibility is derived in the same sense: the record the owner confirmed allows it. Whether a consequence follows from the record is independent of who answered it, since every shown consequence carries that proof: the status says who settled it, and `Settled.derived` says that no one answered it and the proof is all that settles it.

## Worked examples

- [`LeanIntentExamples/Settled.lean`](../LeanIntentExamples/Settled.lean): the words of each status, proved in Lean's kernel, a reason that claims the owner confirmed, and the answerers the owners' log names.
- [`LeanIntentExamples/Sorting.lean`](../LeanIntentExamples/Sorting.lean): `sortedOnlyExplained`, unconfirmed, with the owner's declined answer; `sortingExplained`, confirmed, with one derived consequence and one decided on the owner's behalf.
- [`LeanIntentExamples/Answers.lean`](../LeanIntentExamples/Answers.lean): `attributed`, one answer of the owner's and one on the owner's behalf.
- [`LeanIntentExamples/Recursion.lean`](../LeanIntentExamples/Recursion.lean): `checkDigitsExplained`, unconfirmed, whose one consequence is not settled.

## What is trusted

- That what is recorded is true. These are values a project writes: a record can name as owner a principal who is not one, or keep `.confirmed` after a revision the owner never saw, and the rendering then prints that. `LeanIntent.Trace` decides, from the owners' log, whether an answer's authority traces back to a declared owner, and the rendering says that it does not; tying these values to that log and to a revision is #5's. A consequence's status and an `Attributed` answer to it are separate values, which nothing compares.
- That `LeanIntent.Render` reads from the term what it prints: it reads each status by its constructors, and refuses any other term, and this is argued from its code, since it works on Lean's terms rather than on typed values, and is not stated as a theorem.
- A reason, a gloss and a consequence's name are free text, printed as written. Their author is the one who writes the status, so they can say nothing the status could not; each status is printed on one line of its own, opening with its claim.
