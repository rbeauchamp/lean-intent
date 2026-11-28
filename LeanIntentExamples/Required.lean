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
  o2 := sorting_o2
  o2Run := .proved sorting_o2Run
  o3 := sorting_o3
  o4 := sorting_o4
  freedom := .eq
  o5 := sorting_o5_eq
  comparison := .records sortedOnly (.implies sorting_narrower) (.separates nilSort nilSort_separates)
  additional := [⟨sorting_verdicts⟩]

theorem emptyCases_unrepresentable :
    ¬ ∃ (v : Required sortingDeliverable) (r : String) (s : r.toList.any (!·.isWhitespace) = true)
        (h : ([] : List Proof) ≠ []), v.comparison = .cases [] h r s :=
  fun ⟨_, _, _, h, _⟩ => h rfl

theorem blankDeferred_unrepresentable :
    ¬ ∃ (p : O2RunProof sorting) (h : (" ").toList.any (!·.isWhitespace) = true),
        p = .deferred " " h :=
  fun ⟨_, h, _⟩ => absurd h (by decide +kernel)

theorem bothUnproved_unrepresentable (b : IntentRecord (List Int → List Int)) (r1 r2 : String)
    (s1 : r1.toList.any (!·.isWhitespace) = true)
    (s2 : r2.toList.any (!·.isWhitespace) = true) :
    ¬ ∃ (v : Required sortingDeliverable)
        (h : (ComparisonDirection.unproved r1 s1 : ComparisonDirection sorting b).isProved ||
          (ComparisonDirection.unproved r2 s2 : ComparisonDirection b sorting).isProved = true),
        v.comparison = .records b (.unproved r1 s1) (.unproved r2 s2) h :=
  fun ⟨_, h, _⟩ => by cases h

@[expose] def built : List Lean.Name :=
  [`LeanIntentExamples.Sorting, `LeanIntentExamples.Confirmation,
    `LeanIntentExamples.Implementation, `LeanIntentExamples.Required]

@[expose] def deliverable : DeliverableEntry :=
  ⟨`LeanIntentExamples.Confirmation, ``sortingDeliverable, some ``sorting⟩

@[expose] def implementation : ImplEntry :=
  ⟨`LeanIntentExamples.Implementation, ``sortingImplementation, some ``sortingDeliverable⟩

@[expose] def sortingTheorem (n : Lean.Name) : Cited := .thm ⟨`LeanIntentExamples.Sorting, n⟩

@[expose] def blindRecord : Implementation.Constant := ⟨`LeanIntentExamples.Sorting, ``sortedOnly⟩

@[expose] def entry : Entry :=
  ⟨``sortingRequired, `LeanIntentExamples.Required, some ``sortingDeliverable,
    sortingTheorem ``sorting_o2,
    .proved (sortingTheorem ``sorting_o2Run),
    sortingTheorem ``sorting_o3,
    sortingTheorem ``sorting_o4,
    sortingTheorem ``sorting_o5_eq,
    .records (some blindRecord)
      (.proved (.thm ⟨`LeanIntentExamples.Required, ``sorting_narrower⟩))
      (.proved (.thm ⟨`LeanIntentExamples.Required, ``nilSort_separates⟩)),
    [sortingTheorem ``sorting_verdicts]⟩

theorem located : findings built [deliverable] [implementation] [entry] = [] := by
  decide +kernel

theorem located_listed :
    (report built [deliverable] [implementation] [entry]).theorems =
      [(``sortingRequired, ⟨`LeanIntentExamples.Sorting, ``sorting_o2⟩),
        (``sortingRequired, ⟨`LeanIntentExamples.Sorting, ``sorting_o2Run⟩),
        (``sortingRequired, ⟨`LeanIntentExamples.Sorting, ``sorting_o3⟩),
        (``sortingRequired, ⟨`LeanIntentExamples.Sorting, ``sorting_o4⟩),
        (``sortingRequired, ⟨`LeanIntentExamples.Sorting, ``sorting_o5_eq⟩),
        (``sortingRequired, ⟨`LeanIntentExamples.Required, ``sorting_narrower⟩),
        (``sortingRequired, ⟨`LeanIntentExamples.Required, ``nilSort_separates⟩),
        (``sortingRequired, ⟨`LeanIntentExamples.Sorting, ``sorting_verdicts⟩)] := by
  decide +kernel

theorem undeclaredProject_accepted :
    findings built [{ deliverable with module := `LeanIntentExamples.Scratch }] [implementation]
      [] = [] :=
  findings_nothing

@[expose] def other : DeliverableEntry :=
  ⟨`LeanIntentExamples.Confirmation, `otherDeliverable, some `otherRecord⟩

theorem undeclared_refused :
    findings built [deliverable, other] [implementation] [entry] =
      [.undeclared `otherDeliverable] := by
  decide +kernel

theorem several_refused :
    findings built [deliverable] [implementation]
      [entry, { entry with name := `secondRequired }] =
      [.several ``sortingDeliverable [``sortingRequired, `secondRequired]] := by
  decide +kernel

@[expose] def scratchEntry : Entry :=
  { entry with
      comparison := .records (some blindRecord)
        (.proved (.thm ⟨`LeanIntentExamples.Scratch, `scratch_narrower⟩))
        (.proved (.thm ⟨`LeanIntentExamples.Required, ``nilSort_separates⟩)) }

theorem scratch_refused :
    findings built [deliverable] [implementation] [scratchEntry] =
      [.unbuilt ``sortingRequired `scratch_narrower `LeanIntentExamples.Scratch] := by
  decide +kernel

@[expose] def scratchValue : Entry :=
  { scratchEntry with name := `scratchRequired, module := `LeanIntentExamples.Scratch }

theorem scratchValue_refused :
    findings built [deliverable] [implementation] [entry, scratchValue] =
      [.several ``sortingDeliverable [``sortingRequired, `scratchRequired],
        .requiredUnbuilt `scratchRequired `LeanIntentExamples.Scratch,
        .unbuilt `scratchRequired `scratch_narrower `LeanIntentExamples.Scratch] := by
  decide +kernel

@[expose] def sameNameEntry : Entry :=
  { entry with
      comparison := .records (some blindRecord)
        (.proved (.thm ⟨`LeanIntentExamples.Scratch, ``sorting_narrower⟩))
        (.proved (.thm ⟨`LeanIntentExamples.Required, ``nilSort_separates⟩)) }

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

theorem o2RunDeferred_awaiting_listed :
    findings built [deliverable] [] [{ entry with o2Run := .deferred "awaiting implementation" }] =
        [] ∧
      (report built [deliverable] []
        [{ entry with o2Run := .deferred "awaiting implementation" }]).deferredO2Run =
        [(``sortingRequired, "awaiting implementation")] := by
  decide +kernel

theorem o2RunDeferred_implemented_refused :
    findings built [deliverable] [implementation]
      [{ entry with o2Run := .deferred "awaiting implementation" }] =
      [.o2RunDeferred ``sortingRequired ``sortingDeliverable] := by
  decide +kernel

theorem selfComparison_refused :
    findings built [deliverable] [implementation]
      [{ entry with
          comparison := .records (some ⟨`LeanIntentExamples.Sorting, ``sorting⟩)
            (.proved (.thm ⟨`LeanIntentExamples.Required, ``sorting_narrower⟩))
            (.proved (.thm ⟨`LeanIntentExamples.Required, ``nilSort_separates⟩)) }] =
      [.selfComparison ``sortingRequired ``sorting] := by
  decide +kernel

theorem blindUnbuilt_refused :
    findings built [deliverable] [implementation]
      [{ entry with
          comparison := .records (some ⟨`LeanIntentExamples.Scratch, `scratchBlind⟩)
            (.proved (.thm ⟨`LeanIntentExamples.Required, ``sorting_narrower⟩))
            (.proved (.thm ⟨`LeanIntentExamples.Required, ``nilSort_separates⟩)) }] =
      [.blindUnbuilt ``sortingRequired `scratchBlind `LeanIntentExamples.Scratch] := by
  decide +kernel

theorem blindNotConstant_refused :
    findings built [deliverable] [implementation]
      [{ entry with
          comparison := .records none
            (.proved (.thm ⟨`LeanIntentExamples.Required, ``sorting_narrower⟩))
            (.proved (.thm ⟨`LeanIntentExamples.Required, ``nilSort_separates⟩)) }] =
      [.blindNotConstant ``sortingRequired] := by
  decide +kernel

theorem noComparisonProof_refused :
    findings built [deliverable] [implementation]
      [{ entry with
          comparison := .records (some blindRecord) (.unproved "open") (.unproved "open") }] =
      [.noComparisonProof ``sortingRequired] := by
  decide +kernel

theorem unprovedDirection_listed :
    findings built [deliverable] [implementation]
        [{ entry with
            comparison := .records (some blindRecord)
              (.proved (.thm ⟨`LeanIntentExamples.Required, ``sorting_narrower⟩))
              (.unproved "open reverse direction") }] = [] ∧
      (report built [deliverable] [implementation]
        [{ entry with
            comparison := .records (some blindRecord)
              (.proved (.thm ⟨`LeanIntentExamples.Required, ``sorting_narrower⟩))
              (.unproved "open reverse direction") }]).unprovedComparisons =
        [(``sortingRequired, "backward", "open reverse direction")] := by
  decide +kernel

theorem casesComparison_listed :
    findings built [deliverable] [implementation]
        [{ entry with
            comparison := .cases [.thm ⟨`LeanIntentExamples.Required, ``nilSort_separates⟩]
              "domain in question" }] = [] ∧
      (report built [deliverable] [implementation]
        [{ entry with
            comparison := .cases [.thm ⟨`LeanIntentExamples.Required, ``nilSort_separates⟩]
              "domain in question" }]).casesComparisons =
        [(``sortingRequired, "domain in question")] := by
  decide +kernel

theorem notConstant_refused :
    findings built [deliverable] [implementation] [{ entry with o2 := .term }] =
      [.notConstant ``sortingRequired] := by
  decide +kernel

theorem notTheorem_refused :
    findings built [deliverable] [implementation]
      [{ entry with o2 := .other ⟨`LeanIntentExamples.Sorting, ``sort⟩ }] =
      [.notTheorem ``sortingRequired ``sort `LeanIntentExamples.Sorting] := by
  decide +kernel

end LeanIntentExamples.Required
