import LeanIntent.Statement

/-!
# A statement of the owners' log, and its text

The owner declines the possibility of returning the empty list for every input, shown for the second
revision of the sorting record (`LeanIntentExamples.Answers`). The answer is recorded as a statement
with the owner's words, and `declined_text` gives the characters of its text as the printer writes
them. By `Statement.parse_eq_some_iff`, that text is the only one the parser reads as this
statement, and the parser reads it as nothing else.
-/

namespace LeanIntentExamples.Statements

open LeanIntent

/-- The owner's answer, as a statement. -/
def declined : Statement where
  project := .of "lean-intent"
  id := .of "sorting-empty-list"
  date := ⟨2026, 10, 28, by decide⟩
  source := .words "No: a sort that returns the empty list for every input is not what I mean."
  body := .answer
    { author := ⟨.of "richard", none⟩
      record := "LeanIntentExamples.sorting"
      revision := "sorted: ∀ l, Sorted (f l)\nrearranges: ∀ l, (f l).Perm l"
      consequence := "returning the empty list for every input"
      kind := .possibility
      predicate := "fun f => f = fun _ => []"
      verdict := .declined }

/-- The characters of the text of `declined`, which `Statement.print` makes a string. -/
theorem declined_text : Statement.codec.print declined = chars!"lean-intent statement 1
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
" := by
  decide +kernel

end LeanIntentExamples.Statements
