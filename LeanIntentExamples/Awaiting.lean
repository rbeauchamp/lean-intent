import LeanIntent.Implementation
import LeanIntentExamples.Confirmation

/-!
# The sorting deliverable awaiting its implementation, and what the decision refuses

The sorting deliverable (`LeanIntentExamples.Confirmation.sortingDeliverable`) holds the corrected
sorting record, its explanation and the answer it keeps, all of which its owner confirms before any
implementation exists. Until the project writes its program, it declares that the deliverable awaits
its implementation, in a value of its own, `sortingAwaiting`, with the reason. This module is the
project at that time: it imports the deliverable and no implementation. The deliverable, its
explanation and the owners' log are unchanged by the value, which is declared after the deliverable
its type names, so nothing they hold refers to it.

A reason that says nothing is no value of the type: the field `stated` has Lean's kernel refuse a
blank one (`blank_unrepresentable`).

The decision, given what a build shows of the project (`awaited`, as
`LeanIntent.Implementation.Read` would read it), finds nothing (`awaiting_accepted`), and lists the
deliverable with the value and its reason (`awaiting_listed`). Each change below is refused by name:

* an implementation recorded while the declaration that the deliverable awaits one stays
  (`awaitingImplemented_refused`);
* a second declaration that the same deliverable awaits its implementation
  (`severalAwaiting_refused`);
* a declaration whose type names a deliverable the project does not declare, or a term in place of
  a deliverable (`untiedAwaiting_refused`, `termAwaiting_refused`).

Once the program exists, the project retires the declaration by replacing it with a value of
`Implementation sortingDeliverable`, as `LeanIntentExamples.Implementation` declares; the decision
then finds nothing again (`retired`), by `Implementation.replace_nil_iff`, and no answer's text
changes, since the deliverable is the same constant holding the same terms.
-/

namespace LeanIntentExamples.Awaiting

open LeanIntent LeanIntent.Implementation LeanIntentExamples.Confirmation

/-! ## The declaration -/

/-- Why the sorting deliverable has no implementation yet. -/
def waitReason : String := "The owner has confirmed the record; its program is not written yet."

/-- The sorting deliverable awaits its implementation. The reason's proof that it is not blank is
the default one. -/
def sortingAwaiting : AwaitingImplementation sortingDeliverable where
  reason := waitReason

/-- No value declares the deliverable awaiting its implementation with a blank reason. -/
theorem blank_unrepresentable :
    ¬ ∃ a : AwaitingImplementation sortingDeliverable, a.reason = " " :=
  fun ⟨a, h⟩ => absurd (h ▸ a.stated) (by decide +kernel)

/-! ## What the decision reads, accepts and refuses -/

/-- What the build shows of `sortingAwaiting`. -/
def awaited : AwaitingEntry := ⟨``sortingAwaiting, some ``sortingDeliverable, waitReason⟩

/-- What the build shows, once the program exists, of the value that records it as the
implementation (`LeanIntentExamples.Implementation.sortingImplementation`), which this module does
not import. -/
def implemented : Entry :=
  ⟨`LeanIntentExamples.Implementation.sortingImplementation, some ``sortingDeliverable,
    some ⟨`LeanIntentExamples.Implementation, `LeanIntentExamples.Implementation.sortProgram⟩⟩

theorem awaiting_accepted : findings [``sortingDeliverable] [] [awaited] = [] := by
  decide +kernel

theorem awaiting_listed :
    (report [``sortingDeliverable] [] [awaited]).awaiting =
      [(``sortingDeliverable, ``sortingAwaiting, waitReason)] := by
  decide +kernel

theorem awaitingImplemented_refused :
    findings [``sortingDeliverable] [implemented] [awaited] =
      [.awaitingImplemented ``sortingDeliverable [``sortingAwaiting]] := by
  decide +kernel

theorem severalAwaiting_refused :
    findings [``sortingDeliverable] [] [awaited, { awaited with name := `secondAwaiting }] =
      [.severalAwaiting ``sortingDeliverable [``sortingAwaiting, `secondAwaiting]] := by
  decide +kernel

theorem untiedAwaiting_refused :
    findings [``sortingDeliverable] []
      [awaited, { awaited with name := `otherAwaiting, deliverable := some `otherDeliverable }] =
      [.untiedAwaiting `otherAwaiting] := by
  decide +kernel

theorem termAwaiting_refused :
    findings [``sortingDeliverable] []
      [awaited, { awaited with name := `otherAwaiting, deliverable := none }] =
      [.untiedAwaiting `otherAwaiting] := by
  decide +kernel

/-- Replacing the declaration with the value that records the implementation, which names the same
deliverable and records a constant, leaves the decision finding nothing. -/
theorem retired : findings [``sortingDeliverable] [implemented] [] = [] :=
  (replace_nil_iff (as₁ := []) (as₂ := []) (a := awaited) rfl rfl).mpr awaiting_accepted

end LeanIntentExamples.Awaiting
