# The owners' log

**The owners' log** (`LeanIntent.Statement`): who may answer for a project's intent, and each answer with where it came from, as statements committed in the project, each with exactly one text, whose parser reads back exactly what its printer writes and refuses every other text.

Modules: `LeanIntent/Codec.lean` and `LeanIntent/Codec/Text.lean` (the codecs), and `LeanIntent/Statement.lean` (the statements).

**Complete in this version:** the grammar of the owners' log with its printer, its parser and their round trip.

A project records who may answer for its intent, and each answer, as statements committed in the project (`LeanIntent.Statement`). An answer counts only when a declared owner made it, or a party acting under a delegation that traces back to one, within its scope; the log is the record of where each came from, reviewed like any other change. There are five kinds of statement:

- an owners declaration: the principals, each with the public keys it signs with, if any, and optionally how many owners must approve the next declaration;
- a delegation: who grants it, as an owner or under which delegation; the delegate; the records it covers (all, or those named); whether the delegate may confirm, decline and retract; and whether it may pass the delegation on;
- an answer: who answers, and under which delegation, if any, so an answer the owner gave as owner is told apart from a decision made on the owner's behalf under a delegation; the intent record and the revision of it that was shown; the consequence's name, kind and predicate as they were shown; and the verdict;
- a retraction of an answer, and a revocation of a delegation, each naming the statement it withdraws.

Every statement also names its project, its id, the date, and its source: the owner's words, or a reference to where they are kept. Nothing requires a signature; a project that signs signs the same text.

A reviewer reads a statement's text, the project commits it and a check reads it, so each statement has exactly one text:

| Theorem | What it establishes, for every statement `s` and text `t` |
|---|---|
| `Statement.parse_eq_some_iff` | `parse t = some s` exactly when `print s = t`: the parser accepts exactly the printed texts, reads each as the statement printed, and refuses every other text |
| `Statement.parse_print` | `parse (print s) = some s` |
| `Statement.print_injective` | two statements with the same text are equal |
| `Statement.parseUTF8_eq_some_iff` | the bytes of a committed file are read as `s` exactly when they are the UTF-8 encoding of `print s` |
| `Statement.plain_print` | the text's only control character is the line feed that ends each line, and it holds no line or paragraph separator and no bidirectional formatting character, so each line a display shows is a line the parser reads |

The grammar leaves the printer no freedom: each field has a fixed place and keyword, a list is printed in the statement's order after its length, a number in decimal with no leading zero, a date as `YYYY-MM-DD`, a name of a project, principal or statement in a closed set of ASCII characters, a public key as OpenSSH writes its first two fields, and any other string on one line, or as the number of its lines and then each line after `| `, with `\` and each control, separator or bidirectional formatting character written as an escape. The printer and the parser are assembled from codecs (`LeanIntent.Codec`), each a printer with a parser and a proof that the parser reads back what it prints, so the round trip of the whole grammar holds by construction; `Codec.read` accepts a text only when printing what it read gives the same text back, which makes the parser exact.

An answer, as [`LeanIntentExamples/Statements.lean`](../LeanIntentExamples/Statements.lean) states it and proves its text (`declined_text`):

```
lean-intent statement 1
kind answer
project lean-intent
id sorting-empty-list
date 2026-10-28
words 1
| No: a sort that returns the empty list for every input is not what I mean.
by richard
as owner
record LeanIntentExamples.sorting
revision 2
| sorted: ∀ l, Sorted (f l)
| rearranges: ∀ l, (f l).Perm l
consequence returning the empty list for every input
shown as possibility
predicate 1
| fun f => f = fun _ => []
verdict declined
```

A checkout that rewrites a statement's bytes, by converting its line endings or adding a byte-order mark, makes the parser refuse it; a project keeps its log out of Git's line-ending conversion, for example with `-text` in `.gitattributes`.

Whether an answer's authority traces back to a declared owner within the scope of every delegation on the way is decided by `LeanIntent.Trace` ([Tracing authority](tracing-authority.md)); the text an answer is recorded against is `LeanIntent.Render.answerText`, and recording that text with an answer statement, whose `revision` and `predicate` fields hold what was shown, and refusing an answer whose text has since changed, are #5's; and checking signatures, for a project that signs, is #19's.

## Worked examples

- [`LeanIntentExamples/Statements.lean`](../LeanIntentExamples/Statements.lean): the owner's answer declining the possibility of returning the empty list for every input (an answer of [`LeanIntentExamples/Answers.lean`](../LeanIntentExamples/Answers.lean)), as a statement of the owners' log, and its text.

## What is trusted

- That a statement of the owners' log is true: that its author made it, on its date, as its source says. The log records where each statement came from, and review of the change that commits it checks that, unless the project also signs it. The grammar fixes only what the statement says.
- That a display shows the lines of a statement's text as its line feeds break them. A printed text holds no character that moves, erases, breaks or reorders a line, but characters that look alike stay alike, so two names a reader cannot tell apart may be different names.
