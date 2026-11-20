module

public import LeanIntent.Statement

public section

namespace LeanIntentExamples.Statements

open LeanIntent

@[expose] def declined : Statement where
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
