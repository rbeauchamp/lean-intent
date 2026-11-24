module

public import LeanIntent.Implementation
public import LeanIntentExamples.Confirmation
import all Init.Prelude

public section

namespace LeanIntentExamples.Implementation

open LeanIntent LeanIntent.Implementation LeanIntentExamples.Sorting
  LeanIntentExamples.Confirmation

@[expose] def sortProgram (l : List Int) : List Int := l.mergeSort le

theorem sortProgram_fulfils : sorting.Fulfilled sortProgram := sort_fulfils

@[expose] def sortingImplementation : Implementation sortingDeliverable where
  subject := sortProgram
  fulfils := sortProgram_fulfils

theorem nilSort_unrecordable : ¬ ∃ v : Implementation sortingDeliverable, v.subject = nilSort :=
  fun h => sorting_refutes_nilSort
    (IntentRecord.meets_of_fulfilled (exists_iff.mp h) fun _ hd => nomatch hd)

@[expose] def program : Constant := ⟨`LeanIntentExamples.Implementation, ``sortProgram⟩

@[expose] def entry : Entry := ⟨``sortingImplementation, some ``sortingDeliverable, some program⟩

theorem implemented : findings [``sortingDeliverable] [entry] [] = [] := by
  decide +kernel

theorem implemented_listed :
    (report [``sortingDeliverable] [entry] []).implementations =
      [(``sortingDeliverable, ``sortingImplementation, program)] := by
  decide +kernel

theorem unimplemented_refused :
    findings [``sortingDeliverable] [] [] = [.unimplemented ``sortingDeliverable] := by
  decide +kernel

theorem noDeliverable_refused :
    findings [] [entry] [] = [.noDeliverable, .untied ``sortingImplementation] := by
  decide +kernel

@[expose] def second : Entry :=
  ⟨`secondImplementation, some ``sortingDeliverable,
    some ⟨`LeanIntentExamples.Sorting, ``sort⟩⟩

theorem several_refused :
    findings [``sortingDeliverable] [entry, second] [] =
      [.several ``sortingDeliverable [``sortingImplementation, `secondImplementation]] := by
  decide +kernel

theorem untied_refused :
    findings [``sortingDeliverable]
      [entry, { second with deliverable := some `otherDeliverable }] [] =
      [.untied `secondImplementation] := by
  decide +kernel

theorem termDeliverable_refused :
    findings [``sortingDeliverable] [entry, { second with deliverable := none }] [] =
      [.untied `secondImplementation] := by
  decide +kernel

theorem notConstant_refused :
    findings [``sortingDeliverable] [{ entry with subject := none }] [] =
      [.notConstant ``sortingImplementation] := by
  decide +kernel

theorem oneConstant_accepted :
    findings [``sortingDeliverable, `otherDeliverable]
      [entry, { entry with name := `otherImplementation, deliverable := some `otherDeliverable }]
      [] =
      [] := by
  decide +kernel

end LeanIntentExamples.Implementation
