# The confirmation check

**The confirmation check** (`LeanIntent.Confirmation`, `LeanIntent.Confirmation.Read`): decides, for every deliverable a project declares, whether its current revision is confirmed by answers whose authority traces back to a declared owner, read from the finished build, with theorems stating what it decides.

Modules: `LeanIntent/Confirmation.lean` (the decision and its theorems, which import no more of Lean than the rest of the core) and `LeanIntent/Confirmation/Read.lean` (reading the build, which imports all of Lean).

**Complete in this version:** the deliverable and owners' log a project declares, the decision with its theorems, the reader a checker calls, and the rendering that prints what the log holds. Signatures are optional and tracked in #19; Regula's rule that adopts the check is tracked in Regula.

A consequence counts as confirmed only when a declared owner confirmed it, or a party acting under a delegation that traces back to one; an agent marking its own specification confirmed would remove the one check no proof replaces. This serves every project that adopts the library: each declares its own owner or owners (one person, several or a team, by whatever names it chooses, on any forge or none), with its own agents, and an owner may delegate to another mind, human or AI, for any reason. The owner chose provenance, not cryptography: each answer records who gave it, under which delegation, and its source, committed and reviewed like any other change.

## What a project declares

Two kinds of definition, in the project's own modules:

```lean
import LeanIntent.Confirmation

/-- The owners' log: the text of each statement, as `Statement.print` writes it. -/
def ownersLog : LeanIntent.OwnersLog := ⟨[r#"lean-intent statement 1
kind owners
…
"#, r#"lean-intent statement 1
kind answer
…
"#]⟩

/-- A deliverable: the record, its explanation, the answers it keeps, and the proof it keeps them. -/
def sortingDeliverable : LeanIntent.Deliverable (List Int → List Int) where
  record := sorting
  explanation := sortingExplained
  answers := sortingAnswers
  keeps := sorting_keeps
```

A raw string holds a statement's text unchanged, since a printed text has no control character but the line feed (`Statement.plain_print`). The log is therefore committed text in a module beside the record, reviewed like any change, and the check reads the same text from the build. A record and an explanation must be constants, since an answer names the record by its declared name. A deliverable's `answers` are `Attributed`, naming who gave each, and its explanation records who settled each thing (`Restatement`, `Settled`, [who settled each thing](who-settled.md)); the check compares those with the log.

`Read.answerStatement` writes the text of a new answer to one question of a deliverable, the restatement among them, holding the two texts it must hold:

```lean
import LeanIntent.Confirmation.Read

run_meta do
  Lean.logInfo (← LeanIntent.Confirmation.Read.answerStatement ``sortingDeliverable
    "is Lean's merge sort" (.of "my-project") (.of "merge-sort-answer") ⟨2026, 10, 30, by decide⟩
    (.words "This follows from the restatement confirmed on 2026-10-29.")
    ⟨.of "claude", some (.of "assistant")⟩ .confirmed)
```

## What it decides

- **The owners** are read from the log, never given by a caller. The log holds exactly one owners declaration, which names at least one principal, every statement belongs to that declaration's project, and no two statements share an id (`Declares`). A log with no owner declared passes nothing, a mistyped project on a revocation is refused rather than silently ignored, and a log that repeats an id is refused, naming each id it repeats (`repeated`).
- **An answer counts** (`Counts`) exactly when `LeanIntent.Trace` accepts it by those owners, which is exactly when its authority traces back within the scope of every delegation on the way ([tracing authority](tracing-authority.md)). So the check accepts every confirmation that traces back and refuses every other.
- **Each answer records its source.** An answer that counts and records no source, only blank text, is a finding of the log (`sourceless`): it says nothing of where it came from, so the deliverables are not confirmed until it does. A refused answer needs no source to be refused.
- **Which revision an answer is for.** An answer's `revision` field holds the exact form of the record's rendering without a word of who settled what (`Render.revisionText`), since recording the answer changes those words, and its `predicate` field holds what the consequence's predicate means: the predicate printed exactly, every declaration it reaches printed in full, and the Lean release (`Render.consequenceText`). The check computes both from the build it reads. So an answer to an older revision names another text and does not count, and a definition changed under an unchanged name changes the text.
- **The restatement.** Every revision asks whether its rendering is the owner's plain restatement (`restatement`), so one that shows no consequence, or whose every consequence is derived, still needs an answer. Where the explanation records `Restatement.confirmed n`, that answer is `n`'s, as owner, at this revision (`Revision.Stands`). Where it records none, the answer is a delegate's, under a delegation that covers it; an owner's answer the explanation does not record is refused, so that what it prints is not false.
- **Each consequence shown** has a status that holds (`Revision.Settles`): answered and confirmed at this revision, by the answerer it names; or derived, with no answer at this revision, which `Settled`'s type allows only where the restatement stands as an owner's, and which therefore rests on that owner's confirmation of this revision. A fork, or a consequence not settled, does not pass, and neither does one an answer that counts declines. A status is a field of a consequence the explanation shows, so no status of a consequence the revision no longer has exists.
- **Each answer the deliverable keeps** is backed by an answer that counts, by the answerer `Attributed` names, with the same text and verdict, at any revision; and each answer that counts on its record, but a restatement, is one it keeps.
- **Each status agrees with the answers kept** (`Revision.Agrees`). A status that records an answer names one the deliverable keeps, by the same answerer with the same verdict, and one recorded as derived, which says no one answered it, names no consequence a kept answer answers. So a rendering and an answer's own text say the same of who settled a consequence. A kept answer to a consequence now recorded as derived must be retracted first.
- **A value no deliverable holds** that says who settled something is a finding (`undeclared`), read by `Read.check`: an explanation that records an owner's confirmation, an answer or a derived consequence and is no deliverable's, and an attributed answer, or a list of them, holding one no deliverable keeps. These are what `#render_intent` and `#answer_texts` print from, so a claim of who settled something printed from a project's declarations is asked about. An explanation that claims nothing, whose every consequence is a fork or not settled, may stand outside a deliverable while it is being written.
- **The deliverables are confirmed** (`Confirmed`) when the log declares the owners, there is at least one deliverable, each answer that counts records its source, and each deliverable is confirmed (`Revision.Confirmed`).

The owner confirms the plain restatement and decides the forks; finer consequences are decided on their behalf, and such an answer is a delegate's and must be recorded as one (`Counts.as_owner`): an agent that is no declared owner has no answer that counts without a delegation. That a consequence recorded as derived truly follows from the restatement is not proved here: an agent could record a real fork as derived, which the committed history shows.

| Theorem | What it establishes |
|---|---|
| `findings_eq_nil_iff` | for every log and list of revisions, the decision finds nothing exactly when the deliverables are confirmed |
| `findings_sound` | each thing it finds holds of the log and the revisions, and names the answers concerned |
| `report_findings` | a report's findings are empty exactly when the log's texts are the printed texts of statements that confirm the revisions |
| `parseLog_eq_ok_iff` | a log's texts are read exactly when they are printed statements, each as the statement printed |
| `Confirmed.settled` | every consequence shown has a confirming answer that counts and names the current revision, or a derived status resting on a declared owner's confirmation of that revision's restatement |
| `Confirmed.agrees` | every consequence shown agrees with the answers kept: an answer it records is one of them, and one recorded as derived is answered by none of them |
| `Report.withUndeclared_findings` | what `Read.check` returns finds nothing exactly when no value stands outside a deliverable and the report on the log and revisions finds nothing |
| `Confirmed.restated` | the restatement of a confirmed revision has a confirming answer that counts and names it, so no deliverable passes with an empty or absent confirmation |
| `Confirmed.nodup` | no confirmed log repeats an id |
| `findings_of_repeated` | the decision names each id a log repeats, whatever else is wrong with the log |
| `not_confirmed_of_older` | a log none of whose answers names the revision's text does not confirm it |
| `not_confirmed_of_changed` | a kept answer whose predicate's text no answer holds is refused |
| `not_confirmed_of_dropped` | an answer that counts and that a deliverable does not keep is refused |
| `not_confirmed_of_sourceless` | an answer that counts and records no source is refused |
| `not_confirmed_of_no_declaration`, `not_confirmed_nil` | no owner declared, or no deliverable, confirms nothing |
| `counts_iff` | the decision that an answer counts is `Counts`, which is `Trace.Accepted` |
| `Counts.as_owner`, `Counts.under_delegation` | an answer as owner is a declared owner's; an answer under a delegation cites one that covers it and traces back |
| `logStanding_eq_confirmed`, `logStanding_of_older`, `checked_eq_answered`, `checked_derived` | what the log gives to print says an owner confirmed only where the log holds it at this revision, so a record revised after its owner confirmed it stops printing as confirmed |

Each answer's own decision is `LeanIntent.Trace.check`, whose `check_eq_ok_iff` states that it accepts exactly the answers that trace back, for every log; `Report.decisions` gives it for each answer of the project.

## The rules for what changes after an answer

Each is decided on the owner's behalf, and can be reversed by a later change.

- **A delegation revoked or removed, or an owner removed from the declaration**, takes the authority with it: the answer stops counting, whatever its date, and the check refuses until someone with authority answers again. A date is what its author wrote, so a rule that kept an answer because of its date would let the date keep an authority the project has withdrawn; refusing costs one answer given again, and for a decision on the owner's behalf that is an agent's.
- **Of several owners, one confirming is enough**, as `Trace` reads every owner's authority alike; if the one who confirmed is removed, the rule above applies.
- **A record revised after its owner confirmed it**: the confirmation names an older revision, so it no longer stands, and a derived status rests on nothing until the owner confirms the revision. What the record's explanation holds no longer agrees, and the check refuses it.
- **A definition changed**, in the project or by a new Lean release, changes a kept answer's text, so it is refused, naming the answer, until a party with authority retracts it and answers again. A change that keeps the predicate's text, such as a new property of the record, leaves the kept answers backed, and only asks that the new revision's questions be answered at its text.
- **A kept answer dropped** while its statement still counts is refused, so a deliverable cannot quietly lose a requirement: a person or agent with authority to retract must do so first.
- **A refused answer does not stop a deliverable being confirmed** by answers that count, and is reported by name. A check that failed on any refused answer would refuse answers that trace back, and would let any bad entry hold a project's confirmations.
- **A declined consequence of the current revision stops it**, since each consequence shown holds of the record by proof: the record must change.
- **Several owners declarations are refused.** Owners change by a reviewed edit of the one declaration. A declaration names no author, and only signatures (#19) could settle which of several is in force.
- **A statement added with an id the log already has refuses the log**, naming the id, until one is renamed. `Trace` refuses an answer whose id another statement shares and breaks a link to a delegation whose id another shares, so an unrelated statement must not be able to make an answer refuse and so drop out of what is checked: an owner's decline would no longer stop the deliverable, and answers under a delegation would stop being ones it must keep, with no retraction by anyone with authority. Refusing costs one id renamed. A log so refused has no owners in force, so its report holds no decisions, counted answers or origins, as for every log `inForce` refuses, and its findings say why.

## What a checker reads

`LeanIntent.Confirmation.Read.check mods`, given the project's modules as Lake lists them, reads everything from Lean's environment and parses no source text. The one thing it asks of the file system is which imported modules are Lean's own, where a text's meaning stops, which it reads through the process's search path (`Lean.searchPathRef`, by `Render.leanOwnModules`), the path Lean resolves imports through. It reads nothing from where the running executable lies, reads no environment variable (Lean itself reads `LEAN_MANUAL_ROOT` when it starts, for links in its error messages, which no text prints) and starts no process, so a compiled checker that refuses a process start can call it.

A process sets that path before it imports the project. The `lean` binary does so itself. A compiled program does so by `Lean.initSearchPath` given a toolchain directory, or `Lean.searchPathRef.set`, or `Lean.addSearchPathFromEnv` on the `LEAN_PATH` that Lake gives a program it runs (`lake env`, `lake exe`), which holds Lean's library directory; `Lean.findSysroot` starts `lean --print-prefix` when `LEAN_SYSROOT` is not set. Reading a project from a compiled program also takes what elaboration has already, as the program observed below did: `supportInterpreter = true` on its `lean_exe`, and `enableInitializersExecution` before `importModules (loadExts := true)`. A path that finds no Lean library in it gives an error, never a text.

`Read.renderChecked mods d` prints the deliverable `d`'s rendering with what the log holds of who settled each thing for this revision, in place of what its explanation records. `check` returns a `Report`:

| Field | What it holds |
|---|---|
| `findings` | what is wrong; empty exactly when the deliverables are confirmed and no value saying who settled something stands outside them |
| `decisions` | each answer of the project, with `Trace`'s decision on it |
| `counted` | the answers that count |
| `origins` | each statement of whose words a record's source is, with whether its adoption traces back |
| `tools` | each statement of what an external tool did for a consequence, or what is open |

An origin keeps who wrote a source's words, what they had read of the implementation and of the work that changed it, and the words as adopted, while the statement's own source and date are the owner's adoption. A tool statement keeps the tool's version, configuration, result and cost, or the open item and what depends on it. The record carries both for a checker to read; the check does not require them, since nothing tells it which consequences rest on a tool or which source was adopted.

## Worked examples

- [`LeanIntentExamples/Confirmation.lean`](../LeanIntentExamples/Confirmation.lean): a deliverable of the sorting record, with a log in which the owner confirms the restatement, one consequence is derived from that and an assistant, under a delegation, confirms the other, is confirmed; and the decision refuses, by name, a revised record, a changed definition, no owner, an empty declaration, two declarations, no deliverable, a revoked or removed delegation, a removed owner, an agent's self-confirmation, a dropped answer until it is retracted, a statement of another project, an answer that records no source, a fork, a consequence not settled, a derived consequence someone answered, an owner's confirmation the explanation does not record, a status that disagrees with the answers kept, and an id two statements share, whether an owner's decline's or a delegation's. A worked example uses short texts, since it holds no text of a build, so the reader, its `undeclared` finding and the rendering are not run by it.

## What is trusted

- That a statement's author made it, on its date, as its source says. Review of the change that commits it checks that. Accepted: a dishonest agent could invent an answer, which the history would show; signatures for a project that wants them are #19's.
- That the modules given to `Read.check` are all the project's, and that the deliverables it finds are the current ones: a module left out hides what it declares, and a superseded record kept as a deliverable is asked about like any other. A constant whose type is not one `Read.check` looks for (`Deliverable`, `OwnersLog`, `Explanation`, `Attributed` or a list of those answers) once every definition is unfolded, such as a function returning a deliverable or a structure holding one, is not found, so it is not asked about. An opaque constant or an axiom of one of those types is found, and reading it is an error.
- That a statement removed from the log by a commit is noticed in review: the check reads the log as committed, so removing a revocation restores what it revoked, which the history shows.
- That `#render_intent`, `renderExplanation` and `answerText` print who settled each thing as the record holds it, whatever the log says; they read no log and say so, and only `Read.renderChecked` prints what the log holds. A project whose check passes holds no such value, among the constants `Read.check` finds, that the log contradicts; a term given straight to `answerText` is not a constant, and is printed as given.
- That a consequence recorded as derived truly follows from the restatement: an agent could record a real fork as derived, which the committed history shows. Accepted on the owner's behalf, as the same kind of risk as an invented answer.
- That the rendering prints all of a record's meaning, and `consequenceText` all of a predicate's, as [the rendering](rendering.md#what-is-trusted) lists; so that a change of meaning changes the text is argued from those, not proved. That Lean's compiler runs the decision as defined, and that `Read`, which only reads constants, reads what they are, is argued from its code and was observed on one disposable project, not proved.
- That a project's texts are the same in every kind of process that reads it. The reasons are argued from the code and Lean's source: which modules are Lean's own is decided from the search path and a module's file (`Render.isLeanOwn_iff`), the rule `PROCESS` of `tools/check.lean` finds no call in the library's compiled code that starts a process or asks where it runs or what its environment holds, and the toolchain's version and commit in a text are compiled in. It was observed, at Lean v4.35.0 on 2026-10-31, on one disposable project of one deliverable, with a module of its own under `Lake`. `revisionText` and `consequenceText` gave byte-identical text in each of these: `lean` (the toolchain's binary and elan's), with `LEAN_PATH` set and `LEAN_SYSROOT` unset; `lake env lean`; `lake build`, elaborating a module that computes them under the project's `leanOptions` (`autoImplicit` and `relaxedAutoImplicit` false, `pp.all` true), which the other processes did not set; and a compiled program run by `lake exe`, from `.lake/build/bin`, or copied to another directory, with `LEAN_SYSROOT` as Lake sets it, unset or naming no directory, `LEAN_PATH` set or unset with its search path set by hand, and no `lean` on `PATH`; and both `lean` and a compiled program with a copy of the toolchain's library on the path. `renderChecked` and `check` gave the same under `lake env lean` and that program copied elsewhere, which found nothing in a log of answers `answerStatement` wrote under `lake env lean`. This is sampled, not proved, and no check of this repository runs a compiled reader, so a kind of process not named here is observed before this is claimed of it.
- That the process that writes an answer imports the notation of the process that checks it. The exact form escapes a part of a name that is a token of the notation the process has imported (`Render.printExact`), so a project's notation named like a part of a name its meaning reaches gives `Sorting.«sort»` where its module is imported and `Sorting.sort` where it is not: this was observed. The same follows, by that code, of a token only Lean's `Std` or `Lean` libraries declare, where one process imports them and the other does not. The texts then differ, so the answer does not count and the check refuses, naming it; it never passes. Writing the answer from a process whose imports hold the checker's notation gives the checker's text. Accepted: the failure is a refusal, and the cure is one answer written again.
