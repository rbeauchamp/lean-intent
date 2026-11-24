module

public import LeanIntent.Required
public import LeanIntentExamples.Implementation
import all Init.Prelude

public section

namespace LeanIntentExamples.Required

open LeanIntent LeanIntent.Required LeanIntentExamples.Sorting LeanIntentExamples.Confirmation
  LeanIntentExamples.Implementation

theorem sorting_narrower : ∀ f, sorting.Meets f → sortedOnly.Meets f :=
  fun _ h => sortedOnly_meets.mpr (sorting_meets.mp h).1

theorem nilSort_separates : sortedOnly.Meets nilSort ∧ ¬ sorting.Meets nilSort :=
  ⟨sortedOnly_meets_nilSort, sorting_refutes_nilSort⟩

@[expose] def sortingRequired : Required sortingDeliverable where
  theorems := [⟨sorting_o2⟩, ⟨sorting_o2Run⟩, ⟨sorting_o3⟩, ⟨sorting_o4⟩, ⟨sorting_o5_eq⟩,
    ⟨sorting_verdicts⟩, ⟨sorting_narrower⟩, ⟨nilSort_separates⟩]

theorem empty_unrepresentable : ¬ ∃ v : Required sortingDeliverable, v.theorems = [] :=
  fun ⟨v, h⟩ => v.nonempty h

@[expose] def built : List Lean.Name :=
  [`LeanIntentExamples.Sorting, `LeanIntentExamples.Confirmation,
    `LeanIntentExamples.Implementation, `LeanIntentExamples.Required]

@[expose] def deliverable : Implementation.Constant :=
  ⟨`LeanIntentExamples.Confirmation, ``sortingDeliverable⟩

@[expose] def implementation : Implementation.Constant :=
  ⟨`LeanIntentExamples.Implementation, ``sortingImplementation⟩

@[expose] def sortingTheorem (n : Lean.Name) : Cited := .thm ⟨`LeanIntentExamples.Sorting, n⟩

@[expose] def entry : Entry :=
  ⟨``sortingRequired, `LeanIntentExamples.Required, some ``sortingDeliverable,
    [sortingTheorem ``sorting_o2, sortingTheorem ``sorting_o2Run, sortingTheorem ``sorting_o3,
      sortingTheorem ``sorting_o4, sortingTheorem ``sorting_o5_eq,
      sortingTheorem ``sorting_verdicts,
      .thm ⟨`LeanIntentExamples.Required, ``sorting_narrower⟩,
      .thm ⟨`LeanIntentExamples.Required, ``nilSort_separates⟩]⟩

theorem located : findings built [deliverable] [implementation] [entry] = [] := by
  decide +kernel

theorem located_listed :
    (report built [deliverable] [implementation] [entry]).theorems =
      [(``sortingRequired, ⟨`LeanIntentExamples.Sorting, ``sorting_o2⟩),
        (``sortingRequired, ⟨`LeanIntentExamples.Sorting, ``sorting_o2Run⟩),
        (``sortingRequired, ⟨`LeanIntentExamples.Sorting, ``sorting_o3⟩),
        (``sortingRequired, ⟨`LeanIntentExamples.Sorting, ``sorting_o4⟩),
        (``sortingRequired, ⟨`LeanIntentExamples.Sorting, ``sorting_o5_eq⟩),
        (``sortingRequired, ⟨`LeanIntentExamples.Sorting, ``sorting_verdicts⟩),
        (``sortingRequired, ⟨`LeanIntentExamples.Required, ``sorting_narrower⟩),
        (``sortingRequired, ⟨`LeanIntentExamples.Required, ``nilSort_separates⟩)] := by
  decide +kernel

theorem undeclaredProject_accepted :
    findings built [{ deliverable with module := `LeanIntentExamples.Scratch }] [implementation]
      [] = [] :=
  findings_nothing

@[expose] def other : Implementation.Constant := ⟨`LeanIntentExamples.Confirmation, `otherDeliverable⟩

theorem undeclared_refused :
    findings built [deliverable, other] [implementation] [entry] =
      [.undeclared `otherDeliverable] := by
  decide +kernel

@[expose] def scratchEntry : Entry :=
  { entry with theorems := [.thm ⟨`LeanIntentExamples.Scratch, `scratch_narrower⟩] }

theorem scratch_refused :
    findings built [deliverable] [implementation] [scratchEntry] =
      [.unbuilt ``sortingRequired `scratch_narrower `LeanIntentExamples.Scratch] := by
  decide +kernel

@[expose] def scratchValue : Entry :=
  ⟨`scratchRequired, `LeanIntentExamples.Scratch, some ``sortingDeliverable,
    [.thm ⟨`LeanIntentExamples.Scratch, `scratch_narrower⟩]⟩

theorem scratchValue_refused :
    findings built [deliverable] [implementation] [entry, scratchValue] =
      [.requiredUnbuilt `scratchRequired `LeanIntentExamples.Scratch,
        .unbuilt `scratchRequired `scratch_narrower `LeanIntentExamples.Scratch] := by
  decide +kernel

@[expose] def sameNameEntry : Entry :=
  { entry with theorems := [.thm ⟨`LeanIntentExamples.Scratch, ``sorting_narrower⟩] }

theorem sameName_refused :
    findings built [deliverable] [implementation] [sameNameEntry] =
      [.unbuilt ``sortingRequired ``sorting_narrower `LeanIntentExamples.Scratch] := by
  decide +kernel

theorem deliverableUnbuilt_refused :
    findings built [{ deliverable with module := `LeanIntentExamples.Scratch }] [implementation]
      [entry] =
      [.deliverableUnbuilt ``sortingDeliverable `LeanIntentExamples.Scratch] := by
  decide +kernel

theorem implementationUnbuilt_refused :
    findings built [deliverable] [{ implementation with module := `LeanIntentExamples.Scratch }]
      [entry] =
      [.implementationUnbuilt ``sortingImplementation `LeanIntentExamples.Scratch] := by
  decide +kernel

theorem untied_refused :
    findings built [deliverable] [implementation]
      [entry, { entry with name := `otherRequired, deliverable := some `otherDeliverable }] =
      [.untied `otherRequired] := by
  decide +kernel

theorem termDeliverable_refused :
    findings built [deliverable] [implementation]
      [entry, { entry with name := `otherRequired, deliverable := none }] =
      [.untied `otherRequired] := by
  decide +kernel

theorem notConstant_refused :
    findings built [deliverable] [implementation] [{ entry with theorems := [.term] }] =
      [.notConstant ``sortingRequired] := by
  decide +kernel

theorem notTheorem_refused :
    findings built [deliverable] [implementation]
      [{ entry with theorems := [.other ⟨`LeanIntentExamples.Sorting, ``sort⟩] }] =
      [.notTheorem ``sortingRequired ``sort `LeanIntentExamples.Sorting] := by
  decide +kernel

end LeanIntentExamples.Required
