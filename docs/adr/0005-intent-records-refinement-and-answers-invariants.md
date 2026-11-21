# ADR-0005: Intent records, refinement transfer limits, answers independence, and cone examples

## Status

Accepted

## Context

Core modules (`LeanIntent/Record.lean`, `LeanIntent/Refinement.lean`, `LeanIntent/Answers.lean`, `LeanIntent/Explain.lean`, `LeanIntent/Generic.lean`, `LeanIntent/Progress.lean`, `LeanIntent/Confirmation/Read.lean`) and worked examples (`LeanIntentExamples/Sorting.lean`, `LeanIntentExamples/Transfer.lean`, `LeanIntentExamples/Answers.lean`, `LeanIntentExamples/Cone.lean`) held non-obvious semantic and specification invariants in comments removed in Wave 1 that go beyond what their Lean types alone display.

## Decision

### Intent records (`LeanIntent/Record.lean`)

- **Domain hypotheses vs `Meets`/`Fulfilled`**: Subject-independent world facts are encoded as constant `W → Prop` clauses in `IntentRecord.dom` so every relied-on world fact appears in the owner's restatement (and agent-added ones appear as decisions on the owner's behalf). `Fulfilled` is defined as `r.Dom w → r.Props w` rather than the conjunction `Meets` (`r.Dom w ∧ r.Props w`), because an implementation can only prove its properties under the world's domain hypotheses — it cannot establish facts about the external world.
- **Multi-argument functions in `Shape.bundle` (`Member`)**: Each `Member` is unary (`In → Out`). Multi-argument functions pack arguments together in `In` or leave trailing arguments in `Out`; that choice determines whether `Member.Ignores` under obligation O4 checks ignoring all arguments together or ignoring the first argument.

### Refinement (`LeanIntent/Refinement.lean`, `LeanIntentExamples/Sorting.lean`, `LeanIntentExamples/Transfer.lean`)

- **Domain hypotheses come only from the record**: A refinement link never introduces domain hypotheses of its own; every world fact the deliverable relies on must remain visible in the intent record.
- **Transfer limits**: `Refines` carries guarantees only to the mapping's image, not to the refining implementations themselves — specifically, O3 (refutability) and O5 `.eq` (determinacy) at the intent record do not make a refining specification refutable or determinate when no counterexample to the record lies in that image (`LeanIntentExamples/Transfer.lean`).
- **Implementation specs below the intent record**: While an intent record must be independent of implementation code, a lower-level implementation specification (such as `ImplSpec` in `LeanIntentExamples/Sorting.lean`, stating `∀ l, f l = l.mergeSort le`) may harmlessly name the implementation because its refinement link to the independent intent record (`implSpec_refines`) is machine-checked.

### Answers and undeclared claims (`LeanIntent/Answers.lean`, `LeanIntent/Confirmation/Read.lean`, `LeanIntentExamples/Answers.lean`)

- **Independent specification of `intendedKeeps`**: `keeps_correct` equates `Keeps r answers` with `intendedKeeps`, written by direct pattern matching over `answers` and `r` without reusing any of the six former/helper definitions (`Goals`, `HasInstance`, `Answer.KeptBy`, `IntentRecord.Meets`, `IntentRecord.Dom`, `IntentRecord.Props`), so a bug shared across helpers cannot slip past `keeps_correct`.
- **Self-referential predicate pitfall**: Because a stored `Answer` predicate is a Lean term elaborated in the revision's environment, editing a project definition the predicate names alters the stored answer's meaning without removing it. In particular a confirmed entailment stated through the record it answers (such as `fun f => sorting.Props f`) is kept by every revision made by changing the definition `sorting` itself, whatever the revision changes, because the predicate changes with it. That holds only when the named definition is the one revised: where `sorting` stays fixed and a separate record is checked as the revision, the predicate still means the original properties, and `sortedOnly` does not keep it, since `nilSort` meets `sortedOnly` (`sortedOnly_meets_nilSort`) and not `sorting` (`sorting_refutes_nilSort`, in `LeanIntentExamples/Sorting.lean`). Worked examples (`LeanIntentExamples/Answers.lean`) therefore restrict stored answer predicates (`emptyForEvery`, `rulesOutShort`) to Lean's own standard library so project edits cannot drift their meaning.
- **Undeclared confirmation claims (`Confirmation.Read.undeclaredIn`)**: `undeclaredIn` enumerates the constants the given modules declare whose type reduces to `Explanation _`, `Attributed _` or a list of attributed answers, and names each explanation among them that records a settled or confirmed claim and is no `Deliverable`'s, and each attributed answer, or list of them, holding one that no deliverable keeps. When the project has exactly one owners' log (`projectLog` succeeds), `Confirmation.Read.check` invokes `undeclaredIn` and reports a finding for each, so no declaration that `undeclaredIn` enumerates prints confirmation words the check never asked about (when there is no log or several, `check` returns the log findings immediately and still refuses the project). Its scope is that enumeration of declarations: a term given directly to `LeanIntent.Render.answerText`, which takes an in-memory `Expr` and formats its attribution, is no declaration and is outside it (extending the enumeration to generic `∀ ..., Explanation _` declarations is tracked in #86; replacing the stringly-typed `restatement` sentinel is tracked in #92).

### Cone exclusion non-vacuity and module-file `import all` (`LeanIntentExamples/Cone.lean`)

- Because no Lean theorem can name Lean's live `Environment`, `LeanIntent.Cone`'s theorems quantify over arbitrary `Name → Option ConstantInfo` lookups, and `LeanIntentExamples/Cone.lean` builds a hand-written lookup to prove non-vacuity on concrete cheat/honest records.
- The four `import all` imports in `LeanIntentExamples/Cone.lean` correspond to four functions Lean v4.36.0 does not expose to `module` files: `Init.Prelude` (`Lean.Name.beq`), `Lean.Data.Name` (`Lean.Name.isPrefixOf`), `Lean.PrivateName` (`Lean.privateToUserName`), and `Lean.Declaration` (`Lean.ConstantInfo.isAxiom`).

## Consequences

- In Wave 1, `Record.lean`, `Refinement.lean`, `Answers.lean`, `Explain.lean`, `Generic.lean`, `Progress.lean`, and `LeanIntentExamples/` (`Sorting.lean`, `Transfer.lean`, `Answers.lean`, `Cone.lean`) are cleared to zero comments and `undeclaredIn`'s docstring is removed from `Confirmation/Read.lean`, with each invariant above documented here beside `docs/intent-record.md`, `docs/refinement.md`, `docs/answers.md`, and `docs/cone-exclusion.md`. Remaining docstrings in `Confirmation/Read.lean` stay tracked in `tools/comment-ratchet.json` for a later drain wave.
