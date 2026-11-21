module

public import LeanIntent.Implementation
public import LeanIntentExamples.Confirmation
import all Init.Prelude

public section

namespace LeanIntentExamples.Awaiting

open LeanIntent LeanIntent.Implementation LeanIntentExamples.Confirmation

@[expose] def waitReason : String := "The owner has confirmed the record; its program is not written yet."

@[expose] def sortingAwaiting : AwaitingImplementation sortingDeliverable where
  reason := waitReason

theorem blank_unrepresentable :
    ¬ ∃ a : AwaitingImplementation sortingDeliverable, a.reason = " " :=
  fun ⟨a, h⟩ => absurd (h ▸ a.stated) (by decide +kernel)

@[expose] def awaited : AwaitingEntry := ⟨``sortingAwaiting, some ``sortingDeliverable, waitReason⟩

@[expose] def implemented : Entry :=
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

theorem retired : findings [``sortingDeliverable] [implemented] [] = [] :=
  (replace_nil_iff (as₁ := []) (as₂ := []) (a := awaited) rfl rfl).mpr awaiting_accepted

end LeanIntentExamples.Awaiting
