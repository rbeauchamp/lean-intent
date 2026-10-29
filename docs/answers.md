# The owner's answers

**The owner's answers** (`LeanIntent.Answer`, `LeanIntent.Accepted`): each consequence of a record that is confirmed or declined, by the owner or on the owner's behalf, stays a requirement of every later revision, and a revision that breaks one is refused, by the answer it breaks.

Module: `LeanIntent/Answers.lean`; an answer's canonical text is written by `LeanIntent/Render.lean`.

**Complete in this version:** the owner's answers with the type of the revisions that keep them, and the canonical text of an answer.

**Not yet built**, a separate issue of this repository: tying the answers a project keeps (`LeanIntent.Answer`) to the statements of its owners' log, with the canonical text each was given against (#5). Until #5 lands, nothing in the library establishes that a stored answer is one its project's log records with authority that traces back to a declared owner, or shows whether a stored answer is the owner's own or a decision made on the owner's behalf, or that the owner confirmed a record or a freedom.

The owner validates a record by confirming its plain restatement and deciding the forks it leaves open, as [the README](../README.md#the-owner-and-the-agents) sets out; they are not asked to answer each of its consequences. A consequence (`Consequence`) is a named predicate on the record's subject, shown as an entailment, which every model of the record satisfies, or as a possibility, which some model satisfies, and an answer confirms or declines it (`Answer`). The owner gives an answer where the consequence is a fork their intent does not settle and that changes what they get, such as a degenerate subject the record allows; otherwise the agents give it, as a decision made on the owner's behalf with its reason tied to the owner's intent. Each recorded answer shows which it is in the owners' log, whose answer statement names who gave it: a principal acting as owner, or one acting under the delegation it names ([the owners' log](owners-log.md)). `Answer` itself names no author; until #5 ties it to its statement in the log, a kept answer does not show which it is. Every later revision `r` must keep each stored answer (`Answer.KeptBy`): the answer's unchanged predicate is applied to the subjects that meet `r`, under `r`'s domain hypotheses, never carried over as a fact proved about an earlier revision.

| Consequence | Confirmed: every later revision keeps | Declined: every later revision keeps |
|---|---|---|
| entailment `c` | a theorem: every model satisfies `c` | a countermodel: some model fails `c` |
| possibility `c` | a model that satisfies `c` | a refutation: no model satisfies `c` |

`kept r answers` computes one goal per stored answer, and `keeps_correct` fixes what they state, as the obligations' correctness theorems do. `Accepted answers` is the type of the revisions accepted under the stored answers: no value of it holds a revision that breaks one, and every revision that keeps them all is accepted (`accepted_iff`). A revision fails to keep the stored answers exactly when it keeps the opposite of one of them (`not_keeps_iff`), so every refusal names the answer it breaks and the witness that breaks it; answers that confirm and decline the same consequence refuse every revision until the owner retracts one (`not_keeps_of_conflict`). Whether a revision keeps them depends only on its models (`keeps_congr`): renaming its clauses or its vocabulary, or restating its properties with the same models, loses none, and a revision whose subject has another type cannot be accepted. A revision with no model at all keeps every confirmed entailment and declined possibility; `O2Run`, asked before a deliverable runs, refuses it.

A project keeps its answers by stating them over the record's subject type and declaring a value of `Accepted answers` for its current revision, as [`LeanIntentExamples/Answers.lean`](../LeanIntentExamples/Answers.lean) does:

```lean
def answers : List (Answer (List Int → List Int)) :=
  [⟨⟨"returning the empty list for every input", .possibility, fun f => f = fun _ => []⟩, .declined⟩,
   ⟨⟨"returning [1, 2] for input [2, 1, 1] is ruled out", .entailment, fun f => f [2, 1, 1] ≠ [1, 2]⟩,
    .confirmed⟩]

def sortingAccepted : Accepted answers := ⟨sorting, sorting_keeps⟩
```

where `sorting_keeps : Keeps sorting answers` proves each answer of the current revision. A revision that breaks one leaves `sortingAccepted` without a proof of that answer's goal.

An answer's canonical text, the text it is recorded against, is `LeanIntent.Render.answerText`, given the explanation the answer answers: the answer printed exactly, with its consequence's name, kind and predicate and its verdict; the explanation's name, and its record's statements and the consequences shown with it, exactly as its rendering prints them, with the same headings and glosses; every declaration the record's meaning and the answer reach printed in full, as in the rendering, `Answer.KeptBy` among them, which says what the answer asks of every later revision; and the Lean release whose libraries the rest are. `#answer_texts explained answers` shows the text of each answer of a list to the explanation `explained`. An answer whose meaning, or whose record's meaning, reaches what cannot be printed has no text. Nothing checks that the answer's consequence is one the explanation shows: an answer is printed against the explanation it is given. Recording each text with its answer, and refusing an answer whose text has since changed, is #5's.

## Worked examples

- [`LeanIntentExamples/Answers.lean`](../LeanIntentExamples/Answers.lean): the owner has declined the possibility of returning the empty list for every input and confirmed that returning `[1, 2]` for `[2, 1, 1]` is ruled out; the corrected sorting record keeps both and is accepted, so every accepted revision excludes the empty-list function; a revision that drops the rearrangement property is refused, breaking each answer by a witness; and a revision that renames the vocabulary and restates the two properties as one keeps both.

## What is trusted

- That a stored answer's predicate still means what was confirmed or declined. It is a Lean term, so a revision that changes the body of a definition it uses changes what it says without removing it; a predicate that uses only Lean's own library keeps its meaning while the Lean release does. Such a change changes the answer's canonical text (`answerText`), which prints everything the answer and the record of the explanation it answers reach; recording that text with the answer and comparing it, tying each stored answer to an answer of the owners' log whose authority `LeanIntent.Trace` accepts, and the revision each applies to, are #5's.
- That a project checks its current revision against its stored answers, by declaring a value of `Accepted` for it under all of them; a project that declares none checks nothing.
