---
name: capture-intent
description: >-
  Load before creating, changing, relaying, or recovering an operative account of intent, whoever originated it: accepting a commitment that must survive the conversation, writing or amending a brief, charter, project intent document, the pipeline intent, or an issue, pull request, comment or backlog note that records or changes intent, giving a fixer, sub-agent or collaborator model instructions that carry intent, and answering a decision that changes what makes the work acceptable.
  Also load before acting on newly conveyed or corrected intent whose meaning depends on earlier context (an acknowledgment, a correction, or a reference such as "the second proposal"), even when nothing durable is written, and on /capture-intent.
  Mechanical lookups, conversation that relies on no new or corrected intent, and an unchanged retransmission of an already checked account to the same authorized receiver do not load it.
user-invocable: true
---

# capture-intent

This skill owns the procedure for turning intent into an account that another receiver can use without the conversation it came from: what is wanted and why, the authority behind it, and what remains undecided.
It applies to every intender and receiver: a person, an agent that supervises others, a worker, a reviewer, a collaborator model, a group, or a mind far more capable than any of them.

A proof that an implementation conforms to its specification does not, by itself, establish that the specification expresses the intender's end.
An explicitly authoritative formal object fixes the operative end under its declared interpretation; its authority, its interpretation, its consistency with other obligations and its link to the implementation still have to be established.
When the same available evidence admits ends whose acceptable completed behaviors are disjoint, no policy confined to that evidence can guarantee satisfying the actual end; it can still keep options open or seek evidence that tells the ends apart.
So capture is where intent enters the work, and this skill keeps that entry small, explicit and checkable.

Other owners: your own instructions, those of your project and of the agent you run as, own which instruction governs when two conflict and the format of an instruction that directs another agent's change, and any rule of intent, proof or autonomy stricter than this skill's.
This skill states the principles of intent, proof and autonomy that capture applies, and where an account is kept, so that it needs no other instructions: the division between an intender and a receiver, and when to ask, in the section on questions, consequences and unequal minds; how each claim is labelled in the section on honest closure; and where an account is saved in step 5 of the core procedure.
The tools that carry intent own their own mechanics, such as how a validation pipeline takes its intent input, and the procedures for diagnosing a failure and recording an owner's answers own those steps; for a Lean intent record, [intent-first](../intent-first/SKILL.md) is the procedure that records them, in its step 4.

## Choose the depth first

Choose by what rests on the intent and how costly a misreading is to undo, never by the length of the message.

- **Quick and reversible:** a small commitment, such as acting on "use the second proposal", a one-line backlog note or a wording change.
  Resolve what it refers to, write anything durable so it stands alone, act, and report in one line.
  No questions about delegated choices and no confirmation step.
- **Task:** anything written into a brief, charter, steer, decision answer, issue, pull request or the pipeline intent.
  Apply the core procedure before anything relies on the account.
- **Foundational:** a project's purpose or vision, a standing rule, or an architecture many tasks will build on.
  Also show the intender the restatement of their intent and the forks it leaves open, as the section on questions and consequences describes, and attack the account's boundaries and feasibility.
  Commission an independent challenge only under the owner's authorization or the selected review process; a bounded uncertainty is a reason to use the authorized investigation path, not to create another review gate.

When unsure between two depths, spend more of the receiver's own effort (reading, checking), never more of the intender's attention.

## Core procedure

1. **Establish the sources and the authority.**
   Identify the intender, the receiver, the applicable authority, the acceptance boundary (whose acceptance the account governs) and the current account being changed.
   Read the standing rules, original statements, corrections and recorded decisions that govern this subject, not only the latest message.
   Follow decision-bearing references through their owners, record any material source that is missing or unreadable, and never treat an empty search as proof that no decision exists.
   Stop when the context the present commitment needs is established; reuse a basis already read in this session while it is unchanged.

2. **Resolve meaning in context.**
   Resolve an acknowledgment ("yes", "agreed", "option 2", "the approach we discussed") against the exact thing it accepts, and a correction against the statement it changes, and write that substance out; if the referent cannot be recovered, record it under `Open:` rather than guessing.
   A proposal, recommendation, report or review finding is evidence, not authorization, until the intender adopts it or an existing grant lets the receiver decide it.
   Preserve each supplied example's role and force: required, excluded, illustrative, a witness of a broader criterion, or a member of an intentionally closed set.
   Never close a boundary the intender left open, or open one the intender closed.
   Decide each quantity's role: a bound, a target, a forecast of when something happens, a horizon the design must survive, or an illustration.
   Keep its role and its force.
   Where acceptance depends on a vague term, ground it in a measure or observable the intender would accept, and label that grounding as an interpretation until they do.
   Neither shrink the ambition to fit your expectations nor promote a premise or forecast into an established fact.

3. **Write one operative account per acceptance boundary.**
   Give the context and purpose first, then what must hold and what must not, then preferences and what each trades against.
   Understand the intent in the light of everything the intender has said, then state it as one coherent account in your own words, never as quotations, isolated sentences or bare links, for a future reader who has none of the conversation, so that they can see both what is wanted and why; cite a source only where the text explains what that source contributes.
   State each requirement by the criterion every member of its class meets, over its whole intended domain, including the progress the mission needs, so that doing nothing or meeting only the cited example does not satisfy it; use a list as the boundary only when the intender meant the list to be closed.
   Include the substance of everything the account refers to, so that the account plus the codebase is enough; a committed file, public issue or formal import the receiver can actually read may supply it, and a bare pointer to unavailable context may not.
   Keep apart what the intender expressed, how you interpret it, and what was decided under delegated authority, and label interpretations, recommendations and derived consequences as such.
   Make two entries findable as labeled lines:
   - `Open:` each genuinely unresolved question that could change the work, what depends on it, and who decides it; `none` when none is known.
     A question already decided is not open: it belongs in the account or in the implementation record below.
   - `Sources:` where each commitment came from and the rationale or boundary it contributes, stated so that a reader without private access still has the reason.
     Cite public sources by path, issue, pull request or commit.
     In public text use only citation metadata the audience is authorized to see: a role and date ("the owner's direction of 2026-10-24") may suffice, with a non-revealing disambiguator when two sources would otherwise share it, while the private provenance record identifies the exact source and referent.
     A citation the public cannot inspect says so, and never stands in for the substance it supports.

   Record a decision made under delegated authority in the account only when it changes the conditions under which the work or its effects are acceptable, including execution, resources, evidence, publication and maintenance obligations, and then with the authority that made it and its reason.
   A choice among solutions those conditions already permit remains implementation rationale for the build instructions, the pull request or the worker's own notes, and never becomes a criterion the reviewer judges against.
   A receiver that delegates part of its work writes the child's account at the child's own boundary; that account does not amend the parent's.
   These lines make claims findable; their presence proves neither truth nor completeness, and `Open: none` can be wrong.

4. **Check fidelity in both directions, and feasibility.**
   Compare the account with its sources term by term, and for each requirement construct one case it must admit and one it must rule out:
   - not weaker: no softened obligation, added hedge, narrowed domain, shortened horizon, or quantity or quantifier ("every", "never", "100%") smoothed into an adjective;
   - not stronger: no generalization, sweep or constraint the intender did not ask for, presented as theirs;
   - not vacuous: a system that does nothing, stalls, or meets only the examples fails it, unless a justified no-op is the intended result.

   A restatement must preserve the commitment; an implementation may choose within delegated freedom while keeping the required inputs, outcomes and progress.
   Writing an unauthorized scope change into the account does not authorize it.
   Record whether the account's realizability is established, refuted, or unresolved under its stated assumptions, with the supporting argument or the exact remaining obligation; keep an infeasible or unresolved end at full strength, with the evidence beside it.
   When the work fixes a failure, its defect obligations follow from its causal origin, not its title or label: apply the diagnosis procedure your instructions name.

5. **Persist, then pass it on.**
   Save the account and its provenance through their owning records before dispatch or any other effect that relies on them, where every later receiver and session will find them: a rule that holds everywhere in the instructions every agent loads, a project's purpose and goals in its README or a document its README and its agent instructions point to, and a task's account in the record that carries the task; a conversation is never the only copy.
   If saving is impossible, say so and continue only work that does not rely on it.
   Where a handoff keeps the intent apart from build instructions, the intent section holds the operative account and the build instructions stay outside it.
   Before dispatch, and before any steer or decision answer, check every item that formalizes, narrows, widens or defers an intent term for a case the account requires that the item excludes or defers; then either fix the item or, when the change is authorized, amend the account first with its authority and reason.
   A verifier's acceptance input, such as a validation pipeline's intent, is taken from an identified saved revision of the account through its owning interface, never composed or expanded by a receiver along the way.
   So resolve referents and integrate the intender's later instructions into the saved account before that revision is used.
   Acceptance input and public presentation have separate audience grants: the verifier's input must be authorized for the verifier and its provider, and publication needs its own grant.
   Leaving the account out of a publication is permitted; truncation, unauthorized disclosure or an unproved lossy summary never substitutes for the verifier's acceptance input.
   When an interface limit cannot carry the account losslessly, hold only that dependent handoff and report the limit.
   Raw communications remain the authoritative source where their owner requires that form, as a mandate to keep the owner's own words while the owner is away does; a derived account resolves their meaning beside them and never rewrites that authority.
   Give the next receiver the relevant contract itself or a reference it can resolve; a pointer to a skill missing from the receiver's environment does not discharge the handoff, which is why the section below stands alone.
   Hand on formal claims from a scout, reviewer or collaborator as hypotheses to re-derive from their sources, never as settled intent.
   Delivery, receipt, understanding, authorization and completion are different claims.

## Handing intent on

These rules stand alone, so a receiver that conveys intent onward can apply them without the rest of this skill; a launcher that hands work to an agent without this skill installed carries this section verbatim.
When you convey intent onward - instructions to a sub-agent or a fixer, a gate response, an issue, or a pull-request description - you write an account at that receiver's boundary.
Carry the end at full strength: weaken, hedge or narrow no obligation, smooth no quantifier into an adjective, and present nothing the intender did not ask for as theirs.
State each requirement so that a change that does nothing, or meets only the cited example, does not satisfy it.
Keep each example's role (required, excluded, illustrative, a witness of a broader criterion, or a member of an intentionally closed set) and each quantity's role (a bound, a target, a forecast, a horizon the design must survive, or an illustration).
Keep what was expressed, what you interpret, and what you decided apart, and keep your own implementation choices out of what the receiver judges acceptance against.
Say who decided each thing you direct, as you received it: the intender, an account derived from them, or a named agent on their behalf; and have the receiver write nothing into a record that credits the intender with what they did not express or confirm.
Give the receiver the substance it needs, never a pointer to context it cannot read, and hand on formal claims from a scout, reviewer or collaborator as hypotheses to re-derive.
Relay every constraint you cannot evaluate exactly as given, never coarsened or dropped.
Public text carries no private source text, private paths, or confidential facts paraphrased from private sources.
The pipeline intent is not yours to write: pass exactly what your instructions name, and report anything in it that seems wrong or missing to whoever gave you those instructions instead of adding to it.

## Questions, consequences and unequal minds

Apply the governing authority rules before weighing the cost of a question: an authorization they require is never optional, however cheap or reversible the effect looks.
Within delegated reversible work, never ask the intender to choose, approve or confirm a step: act on the reading the evidence best supports, and report the choice and its reason.
Ask about the intent itself (what is wanted and why) only when unresolved meaning materially prevents a faithful choice.
Ask one sharp question, give each option's consequences and your recommendation with its evidence, and keep doing the work that does not depend on the answer.
Silence is not confirmation.
The intender works at the level of intent, and that level is not fixed: they state intent wherever they actually hold it, and for a detail a receiver invented, their intent sits one level up.
As with an API and its implementation, what the intender states and confirms is the system's contract: preconditions on its inputs, postconditions on its outcomes and mission results, and its invariants; specifications of internal functions below that level are the receiver's design, which the receiver owns and may change.
For foundational or consequential accounts, show the intender a plain restatement of their intent, with concrete cases of what it requires, allows and rules out, and the forks it leaves open, alongside any formal statement, and have them confirm that restatement, which is their intent rather than a step and so is never skipped.
A fork is real when the intent does not settle it and its branches change what the intender gets; two independent readings that disagree on something the intender would care about are one sign of one.
Real forks, one-way doors and trades of quality for cost go to the intender, never decided on their behalf.
A consequence of a formal statement below the intender's level is never shown to them for confirmation: the receiver checks it against the confirmed restatement and records it in the specification or implementation record as decided on the intender's behalf, with its reason tied to their intent, and never presents it as theirs.
One that contradicts the confirmed restatement is a defect in the formal statement, and one the restatement leaves unsettled that changes what the intender gets is a fork.
A consequence therefore has three statuses: derived from the account under named assumptions, confirmed by the intender, and decided on the intender's behalf; derivation is independent of the other two, which exclude each other.
A consequence the intender never saw is not their confirmation: a derived or decided consequence guides reversible work but is not their endorsement, and a surprising one is a reason to disclose it, not to pretend it was meant.
A confirmation the account does not entail is a requirement to meet, never a theorem already proved: record the gap.
Capability and the assurance required are relative to the obligation at hand, not a ranking of minds.
A receiver more capable than its intender gains no authority from that: it preserves the end as given, distinguishes the purpose from any means the intender stated, and discloses with evidence any sign, derived against the intender's own objectives and assumptions, that the end is infeasible, inconsistent or self-defeating, or that a stated means defeats or bottlenecks the purpose, recommending a correction while keeping the stated means until the intender changes it.
Delegation already granted does not lapse because the intender cannot follow a choice made within it, and incomprehension never creates new consent.
When a consequential distinction exceeds what the intender can follow directly, the receiver projects it onto observable invariants, failure bounds or verifier results at a point the intender does understand, and records the limit that remains.
A receiver less capable than its intender relays every constraint it cannot evaluate exactly as given, never coarsened or dropped.
Before an irreversible effect, or one nobody can check afterwards, it requires evidence that entails the obligation itself under named trusted boundaries, such as a certificate an authorized checker accepts; a witness of one case does not establish a universal obligation, and personal comprehension is not required.
Without that assurance it names the dependent effect and the unresolved obligation, routes it to an authorized capable receiver or checker, withholds only that effect, and continues compatible work.
Present the material alternatives and the assumptions behind their selection; explain unequal evidence rather than presenting the options as equal.

## Revisions and source custody

Keep the operative account current and identify its acceptance revision.
Retain each predecessor with its authority, reason and affected dependents in the discoverable revision history kept with the account's durable record, and keep that history out of the acceptance input.
Never rewrite an earlier statement to make it appear to support a later reading.
A revision never silently overwrites a change made since its author's basis, and never becomes operative before its predecessor and authority are recoverable.
The basis includes the decision-bearing definitions and assumptions the account imports, so an unchanged text over a changed definition is a new revision.
Distinguish editorial changes from changes to acceptance.
A consequence the intender confirmed is a requirement of the revision it confirms, which every later refinement must go on meeting.
An authorized later instruction replaces it when the intended replacement is unambiguous, even if the instruction does not name the consequence or its record ("for this task, replace CSV output with JSON"): the receiver records what it supersedes and the affected dependents.
A contradiction that arrives only indirectly, or from an authority below the one that confirmed it, or that leaves authority, meaning or scope unresolved, is surfaced, never treated as a replacement ("make synchronization seamless" does not lift a confirmed offline requirement).
A consequence decided on the intender's behalf is the receiver's design, not a requirement of the account: the receiver may revise it with a recorded reason while the confirmed restatement still holds.
A decision answer or steer that changes acceptance amends the account before anything acts on it; the owner's own words stay as source evidence beside it, and a validation run already under way is reconciled with the change as below.
Evidence applies only to the acceptance revision and result it assessed, and every dependent effect, landing included, needs evidence applicable to the operative revision at the moment it is authorized.
A changed account does not inherit a previous run's authority because the branch or the code is unchanged.
A digest supports identification under its stated assumptions; byte identity, even established directly, does not establish equivalence of meaning or evidence applicability.
Treat a mismatch between a run's assessed revision and the current account as evidence whose applicability is unresolved, and re-validate or give an explicit transfer argument.
Keep original communications and what they refer to in a private provenance record you keep; task sources follow the task's durable record, and project or charter sources live in a record that outlives any one task.
Keep them while the account or anything depending on it relies on them.
Before the owner of that storage retires (a task's cleanup, a retired agent's storage), transfer and verify custody of every source or revision a surviving dependent still needs; a private or ignored location alone establishes neither access control nor retention.
Access is by grant, and being a model, a reviewer or a subprocess confers none.
Public artifacts carry an authorized account, never private source text, private paths, or confidential facts, identities or incidents paraphrased from private sources; mark a reduced public account as a projection, and never let it replace the acceptance a verifier uses.
After a reset, read the current account, its open items and recorded decisions before acting.
Change an earlier recommendation only with a recorded reason: new evidence, changed authority or corrected reasoning.

## Formal and collective handoffs

Intent may arrive as words, a demonstration, a formal object, an interaction or a concept the intender has just made; keep it in the form it was given, beside any restatement.
Where intent is already formal, keep its semantic domain, definitions, environment assumptions, required inputs, progress, authority, resource envelope and trusted boundaries, and connect its proofs to the delivered implementation.
Where two authoritative representations of one intent both have formal semantics, their equivalence is itself a proof obligation.
For a restatement, establish equivalence where the formalism allows; for a delegated implementation, establish refinement and realizability, since subset inclusion alone admits an impossible or idle child contract.
For several receivers, give each the shared purpose plus its own obligation and resource share, and state the environment and coordination assumptions under which their contracts compose to the mission; replication never multiplies an authority or resource grant, and disjoint files alone do not establish safe composition.
For several intenders, apply their authorized combination and conflict procedure.
Intersecting every proposal, counting copies of one principal, or choosing the most ambitious statement creates no authority; where obligations conflict, isolate the conflicting core, continue the compatible authorized work, and surface the conflict to whoever may decide it.
For a round designated as blind independent discovery, give every peer the same primary facts and prompt without your conclusions, preserve your own draft before you see theirs, and disclose any earlier exposure; cross-review rounds deliberately exchange conclusions under their owning protocol.
Where your project or tools have a procedure for such rounds, it owns sealing drafts and the rounds; [intent-first](../intent-first/SKILL.md)'s step 3 is one, for a second model's blind formalization of a Lean intent record.

## Honest closure

State which claims are constructed, mathematically argued, machine-checked, observed, assumed or unresolved.
A field check, digest, manifest or review verdict does not establish fidelity of meaning.
Find enforcement boundaries by function, through their owning interfaces: every operation that admits or changes a commitment, transfers it, accepts evidence against it, or authorizes an effect on it.
Never claim complete enforcement while another writer or handoff remains outside the contract.
Treat each demonstrated capture failure (a valid finding or owner correction traced to an account or relay) as a counterexample to the step that let it through.
Route it through the diagnosis and repair owners: correct it within your existing authority, or hand the exact required change to the owner of that step.
Record it through your project's existing retrospective where one is configured, without adding another schedule, threshold or evaluation run.
