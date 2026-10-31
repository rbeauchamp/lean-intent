# Tracing authority

**Tracing authority** (`LeanIntent.Trace.check`): a decision, with theorems stating what it decides, whether each answer of the owners' log was given by a declared owner, or under a chain of delegations that traces back to one within the scope of every delegation on the way, each passed on only where it may be and none revoked, and whether a retraction with such authority withdrew it; each refusal names the answer and why, such as the first link that breaks or the retraction that withdrew it.

Module: `LeanIntent/Trace.lean`.

**Complete in this version:** the decision whether each answer's authority traces back to a declared owner with the theorems stating what it decides, what each refusal says and where it is monotone.

`LeanIntent.Trace.check project owners log s` decides whether the statement `s` is an answer that counts, given the project, the owners declaration in force and the statements of the project's log. Every statement records who made it: a principal acting as an owner, or acting under the delegation it names, which is how an answer of the owner's own is told apart from a decision made on the owner's behalf. So an answer names the one chain its authority rests on, the delegation it acts under, the delegation that one was granted under, and so on, and the decision follows that chain from the answer, testing each link in turn:

- the one statement of the project with the link's id is a delegation, and its delegate is the principal acting under it;
- no revocation of the project revokes it, made by the principal who granted it or by a declared owner acting as owner;
- its scope covers the answer's record, as every record or by its exact name, and lets its delegate do what the answer does, confirm or decline;
- it may be passed on, unless it is the delegation the answer itself acts under;
- and the chain ends at a declared owner acting as owner.

The answer must also be the one statement of the project with its id, and no retraction may withdraw it whose own authority traces back by the same rules, for retracting an answer on the answer's record. `LeanIntent.Trace.checkLog project owners log` gives the decision on every answer of the project in the log, in the log's order.

| Theorem | What it establishes |
|---|---|
| `check_eq_ok_iff` | for every project, owners declaration, log and statement, `check` accepts exactly the accepted answers (`Accepted`), whose authority is defined by the inductive `Chain`: it accepts only those (soundness) and every one of them (completeness) |
| `mem_checkLog` | `checkLog` pairs each answer of the project in the log with `check`'s decision on it, and holds nothing else |
| `chain_iff_leads` | an authority traces back exactly when links that all hold lead from it to a declared owner acting as owner |
| `check_eq_error` | every refusal names the answer, and its reason holds: the statement is not the one of the project with its id, or not an answer; or the first link of its chain that breaks, every link before it holding, and the test that link fails; or a retraction that withdraws it with authority that traces back |
| `Fails.not_chain`, `Leads.not_chain` | a link that breaks breaks every chain through it |
| `Chain.no_cycle` | no chain returns to a link it has passed, so delegations granted under each other give no authority |
| `Chain.append_fresh` | a statement that is no revocation, added with an id no statement of the log has, keeps every chain |
| `Chain.of_append` | a statement that is no delegation, added to the log, makes no chain, so a revocation only removes authority |
| `Accepted.of_append_retractions` | a retraction added with an id no statement of the log has accepts no answer the log refused |

The decision stops on every log: it passes each id of the log at most once, and refuses a chain that returns to a link it has passed. Acceptance is not monotone everywhere: revoking a delegation voids a retraction made under it, which restores the answer it retracted; adding a delegation can make such a retraction count; and an owners declaration with more owners can make a revocation count.

It reads only the statements of the project. A reference to an id that no statement of the project has, or that more than one has, breaks its link, and an answer whose id another statement of the project shares is refused, so no reference is ambiguous. It reads no date: a revocation voids every act made under the delegation, before or after it. It reads no source and no key. Which owners declaration is in force is the caller's to give; [the confirmation check](confirmation.md) gives it from the log's one declaration, and a log with several is refused, since only signatures (#19) could settle which is in force, as is a log that repeats an id; and that each statement's author made it is checked by review of the change that commits it, as for every statement of the log.

## Worked examples

- [`LeanIntentExamples/Trace.lean`](../LeanIntentExamples/Trace.lean): the owner delegates the sorting record to an assistant, who passes confirming on to a reviewer that may not pass it on; the owner's answer and the reviewer's confirmation through two links are accepted, and the decision refuses, each at the first link that breaks, the reviewer declining, the reviewer answering for another record (at the assistant's link), a delegate of the reviewer, a principal that calls itself an owner, the reviewer once its delegation is revoked, and an answer under two delegations granted under each other, and refuses the owner's answer, by the retraction, once the assistant retracts it.

## What is trusted

- That the owners declaration given to `LeanIntent.Trace.check` is the one in force for the project, and the log given holds every statement the project has committed: the decision is relative to both, and gathering them is the caller's, which [the confirmation check](confirmation.md) does. A log missing a revocation or a retraction can accept an answer the whole log refuses. That Lean's compiler runs the decision as it is defined: its theorems are about its definition.
