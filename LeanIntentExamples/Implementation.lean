import LeanIntent.Implementation
import LeanIntentExamples.Confirmation

/-!
# The implementation of the sorting deliverable, and what the decision refuses

The sorting deliverable (`LeanIntentExamples.Confirmation.sortingDeliverable`) holds the corrected
sorting record, its explanation and the answer it keeps, all of which its owner confirms before any
implementation exists. Once the project writes its program, `sortProgram`, it records that program
as the deliverable's implementation in a value of its own, `sortingImplementation`, with the proof
that the program fulfils the record (`sortProgram_fulfils`). The deliverable, its explanation and the
owners' log are unchanged by it, so every text an answer holds is too: the explanation's meaning
reaches `sort`, through the consequence the assistant answered, and never `sortProgram`, which is
declared after it.

The value's type fixes what its proof proves: that the subject it records fulfils the record. So the
function returning the empty list, which fails the record, cannot be recorded as the implementation
by any proof (`nilSort_unrecordable`).

The decision, given what a build shows of the project (`entry`, as `LeanIntent.Implementation.Read`
would read it), finds nothing (`implemented`), and lists the deliverable with the value and the
program's module and name (`implemented_listed`). Each change below is refused by name:

* no value recording the implementation (`unimplemented_refused`), and no deliverable
  (`noDeliverable_refused`);
* a second value recording another implementation of the same deliverable, whichever constant it
  records (`several_refused`);
* a value whose type names a deliverable the project does not declare, or a term in place of a
  deliverable (`untied_refused`, `termDeliverable_refused`);
* a value whose subject is a term rather than a constant (`notConstant_refused`).

A constant may implement two deliverables, each value proving its own record of it
(`oneConstant_accepted`).
-/

namespace LeanIntentExamples.Implementation

open LeanIntent LeanIntent.Implementation LeanIntentExamples.Sorting
  LeanIntentExamples.Confirmation

/-! ## The implementation -/

/-- The program the project runs to sort, written once the record was confirmed: Lean's merge sort. -/
def sortProgram (l : List Int) : List Int := l.mergeSort le

/-- The program fulfils the record. Its proof is the one of `sort`, which is the same function by
definition, so the proposition proved is this one, about `sortProgram`. -/
theorem sortProgram_fulfils : sorting.Fulfilled sortProgram := sort_fulfils

/-- The sorting deliverable's implementation: the program, and the proof that it fulfils the
record. -/
def sortingImplementation : Implementation sortingDeliverable where
  subject := sortProgram
  fulfils := sortProgram_fulfils

/-- No value records the function returning the empty list as the implementation: it does not fulfil
the record, and a value's proof is of the subject it records. -/
theorem nilSort_unrecordable : ¬ ∃ v : Implementation sortingDeliverable, v.subject = nilSort :=
  fun h => sorting_refutes_nilSort
    (IntentRecord.meets_of_fulfilled (exists_iff.mp h) fun _ hd => nomatch hd)

/-! ## What the decision reads, accepts and refuses -/

/-- The program, by its module and its name, as the build shows it. -/
def program : Constant := ⟨`LeanIntentExamples.Implementation, ``sortProgram⟩

/-- What the build shows of `sortingImplementation`. -/
def entry : Entry := ⟨``sortingImplementation, some ``sortingDeliverable, some program⟩

theorem implemented : findings [``sortingDeliverable] [entry] = [] := by
  decide +kernel

theorem implemented_listed :
    (report [``sortingDeliverable] [entry]).implementations =
      [(``sortingDeliverable, ``sortingImplementation, program)] := by
  decide +kernel

theorem unimplemented_refused :
    findings [``sortingDeliverable] [] = [.unimplemented ``sortingDeliverable] := by
  decide +kernel

theorem noDeliverable_refused :
    findings [] [entry] = [.noDeliverable, .untied ``sortingImplementation] := by
  decide +kernel

/-- A second value, recording `sort` as the implementation of the same deliverable. -/
def second : Entry :=
  ⟨`secondImplementation, some ``sortingDeliverable,
    some ⟨`LeanIntentExamples.Sorting, ``sort⟩⟩

theorem several_refused :
    findings [``sortingDeliverable] [entry, second] =
      [.several ``sortingDeliverable [``sortingImplementation, `secondImplementation]] := by
  decide +kernel

theorem untied_refused :
    findings [``sortingDeliverable] [entry, { second with deliverable := some `otherDeliverable }] =
      [.untied `secondImplementation] := by
  decide +kernel

theorem termDeliverable_refused :
    findings [``sortingDeliverable] [entry, { second with deliverable := none }] =
      [.untied `secondImplementation] := by
  decide +kernel

theorem notConstant_refused :
    findings [``sortingDeliverable] [{ entry with subject := none }] =
      [.notConstant ``sortingImplementation] := by
  decide +kernel

/-- Two deliverables, each implemented by its own value, recording the same constant. -/
theorem oneConstant_accepted :
    findings [``sortingDeliverable, `otherDeliverable]
      [entry, { entry with name := `otherImplementation, deliverable := some `otherDeliverable }] =
      [] := by
  decide +kernel

end LeanIntentExamples.Implementation
