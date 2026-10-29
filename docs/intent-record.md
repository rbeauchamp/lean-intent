# The intent record

**An intent record** (`LeanIntent.IntentRecord`): named properties of one deliverable's subject, over a vocabulary of predicates, under named domain hypotheses, written before the implementation exists.

Module: `LeanIntent/Record.lean`. Writing a record and proving its obligations is shown under [Using it](../README.md#using-it) in the README.

**Complete in this version:** the intent record.

## What is trusted

Besides [what the README lists](../README.md#what-is-trusted), about every record:

- That a record's shape is the one its subject has: a subject with state declared as a plain value is asked nothing by O4. The degenerate check, fixed by the subject's type rather than its declared shape, narrows this. For a covered step without output (`S → S`, `S → I → S`) the step that does nothing is a projection, so a record it meets reports it to the owner, though it does not refuse the record as O4 would. A step with output (`S → O × S`, `S → I → O × S`) does nothing by returning any output with the state unchanged. The class does not generally enumerate these state-preserving subjects, although some coincide with its constants or projections: for `Unit → Bool × Unit`, every constant preserves the state and is in the class. The shape therefore stays trusted.
- That the domain hypotheses are true of the world: those the owner states are confirmed with the restatement of their intent, and one an agent adds is a decision made on the owner's behalf, recorded with its reason; a hypothesis that excludes the subject that does nothing, or all but one model, would make O4 or O5 hold vacuously, one that excludes a degenerate subject keeps the degenerate check from reporting it, and one that excludes the subject of a declined possibility keeps that answer vacuously.
