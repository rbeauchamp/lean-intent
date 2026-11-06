import LeanIntent.Required
import LeanIntentExamples.Implementation

/-!
# The theorems the sorting deliverable relies on, and what the decision refuses

The sorting deliverable (`LeanIntentExamples.Confirmation.sortingDeliverable`) rests on theorems
the intent-first procedure has its project prove: the corrected sorting record's obligations and
the verdicts of its degenerate subjects (`LeanIntentExamples.Sorting`), and here a comparison of
that record with another reading of the owner's words, the record that forgets the rearrangement
property, standing in for a second model's blind formalization: every subject meeting the record
meets that reading (`sorting_narrower`), and the empty-list function meets that reading and fails
the record (`nilSort_separates`). The project names them for the deliverable in a value of its own,
`sortingRequired`, which lists each theorem by its name. A value listing no theorem cannot be
declared (`empty_unrepresentable`).

The decision, given what a build shows of the project (`deliverable`, `implementation` and
`entry`, as `LeanIntent.Required.Read` would read them) and the module names the build lists
(`built`), finds nothing (`located`), and lists each theorem with the module that declares it
(`located_listed`); with nothing declared it finds nothing (`nothing_accepted`, by
`findings_nothing`, which holds whatever the build lists). Each change below is refused by name:

* no value naming the deliverable's theorems, which the refusal says to declare
  (`undeclared_refused`);
* a comparison theorem declared in a module the build does not list, such as a scratch file
  (`scratch_refused`), and a theorem of the very name of one in a built module, declared in such a
  module instead, which the decision reads by the module that declares it, never by its name
  (`sameName_refused`);
* the deliverable, or the value recording its implementation, declared in a module the build does
  not list (`deliverableUnbuilt_refused`, `implementationUnbuilt_refused`);
* a value whose type names a deliverable the project does not declare, or a term in place of a
  deliverable (`untied_refused`, `termDeliverable_refused`);
* an entry that is a term rather than a theorem's name, and a constant that is not a theorem
  (`notConstant_refused`, `notTheorem_refused`).
-/

namespace LeanIntentExamples.Required

open LeanIntent LeanIntent.Required LeanIntentExamples.Sorting LeanIntentExamples.Confirmation
  LeanIntentExamples.Implementation

/-! ## The theorems, and the value naming them -/

/-- Every subject meeting the sorting record meets the reading that forgets the rearrangement
property. -/
theorem sorting_narrower : ∀ f, sorting.Meets f → sortedOnly.Meets f :=
  fun _ h => sortedOnly_meets.mpr (sorting_meets.mp h).1

/-- The empty-list function meets the reading that forgets the rearrangement property, and fails
the sorting record. -/
theorem nilSort_separates : sortedOnly.Meets nilSort ∧ ¬ sorting.Meets nilSort :=
  ⟨sortedOnly_meets_nilSort, sorting_refutes_nilSort⟩

/-- The theorems the procedure requires of the sorting deliverable, each by its name. -/
def sortingRequired : Required sortingDeliverable where
  theorems := [⟨sorting_o2⟩, ⟨sorting_o2Run⟩, ⟨sorting_o3⟩, ⟨sorting_o4⟩, ⟨sorting_o5_eq⟩,
    ⟨sorting_verdicts⟩, ⟨sorting_narrower⟩, ⟨nilSort_separates⟩]

/-- No value of `Required` lists no theorem. -/
theorem empty_unrepresentable : ¬ ∃ v : Required sortingDeliverable, v.theorems = [] :=
  fun ⟨v, h⟩ => v.nonempty h

/-! ## What the decision reads, accepts and refuses -/

/-- Module names a build of the worked examples lists: those of the modules this example reads. -/
def built : List Lean.Name :=
  [`LeanIntentExamples.Sorting, `LeanIntentExamples.Confirmation,
    `LeanIntentExamples.Implementation, `LeanIntentExamples.Required]

/-- The deliverable, by its module and its name, as the build shows it. -/
def deliverable : Implementation.Constant :=
  ⟨`LeanIntentExamples.Confirmation, ``sortingDeliverable⟩

/-- The value recording the deliverable's implementation, by its module and its name. -/
def implementation : Implementation.Constant :=
  ⟨`LeanIntentExamples.Implementation, ``sortingImplementation⟩

/-- A theorem of the sorting record, by its module and its name. -/
def sortingTheorem (n : Lean.Name) : Cited := .thm ⟨`LeanIntentExamples.Sorting, n⟩

/-- What the build shows of `sortingRequired`. -/
def entry : Entry :=
  ⟨``sortingRequired, some ``sortingDeliverable,
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

theorem nothing_accepted : findings built [] [] [] = [] := findings_nothing

theorem undeclared_refused :
    findings built [deliverable] [implementation] [] = [.undeclared ``sortingDeliverable] := by
  decide +kernel

/-- The comparison theorem, declared instead in a scratch module the build does not list. -/
def scratchEntry : Entry :=
  { entry with theorems := [.thm ⟨`LeanIntentExamples.Scratch, `scratch_narrower⟩] }

theorem scratch_refused :
    findings built [deliverable] [implementation] [scratchEntry] =
      [.unbuilt ``sortingRequired `scratch_narrower `LeanIntentExamples.Scratch] := by
  decide +kernel

/-- The entry as the build would show it if the theorem of `sorting_narrower`'s name were declared
in the scratch module, which an environment importing that module records. -/
def sameNameEntry : Entry :=
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
      [.notTheorem ``sortingRequired ``sort] := by
  decide +kernel

end LeanIntentExamples.Required
