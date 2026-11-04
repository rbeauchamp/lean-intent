# Interim stand-in for a lean-intent check not yet built

lean-intent's degenerate-subject check (`docs/degenerate-subjects.md`) states its verdicts only of a subject whose type it covers; for any other type Lean reports that it cannot synthesize `Covered`, so no verdict about it can be stated.
The section below stands in for that check on every such type; lean-intent's document for the check says which declared types its deriving handler refuses, and why.
A stand-in here is a class you prove theorems over, not a decision procedure with a theorem stating what it decides: the section says what it decides and what it leaves undecided, so that your report claims no more.

## Degenerate implementations

The class is fixed by the subject's type and never chosen per record.
Prove, family by family, either that every member fails the record or which members meet it; one universal theorem covers a whole family, however many members it has, so prefer it to listing members.

For a function of type `A₁ → … → Aₙ → B` (shape `.function`):

- **Constant functions**: prove `∀ c : B, ¬ r.Meets (fun _ … _ => c)`.
  Where some constants meet the record, find which: all of them where `B` has finitely many values, and otherwise at least the empty output where `B` has one (such as `[]`, `#[]`, `""`, `none` or `0`), `default` where `B` has an `Inhabited` instance, and each constructor of `B` that takes no arguments.
- **The identity**, where `n = 1` and `A₁` is `B`: prove `¬ r.Meets (fun a => a)` or that it meets the record.
- **Projections**: for each argument whose type is `B`, the function returning that argument; and for each argument whose type is a structure, the function returning each of its fields whose type is `B`.

For a step (`.step`, `.stepOn`, `.action` or `.actionOn`): O4 already asks that every subject leaving the state unchanged fail the record; add the constant next states, as for constant functions above, and for an action each constant output.

For a `.value`: the empty value and `default`, where its type has them.

Each member that meets the record is a consequence for step 4.
List in the report every family checked and, where a family was not covered by a universal theorem, which members were, so the report shows what this interim rule left unchecked.
