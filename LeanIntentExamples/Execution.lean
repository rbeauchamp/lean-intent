import LeanIntent.Execution
import LeanIntentExamples.Implementation

/-!
# The executable that runs the sorting deliverable, and what the decision refuses

The sorting deliverable (`LeanIntentExamples.Confirmation.sortingDeliverable`) is implemented by
`sortProgram`, which `LeanIntentExamples.Implementation.sortingImplementation` records with its
proof. A project that ships the program as an executable, say a Lake target `sorter` whose root
module `Sorter` declares `main`, says so in a value of its own, `sorterRuns`, naming the target. The
deliverable, its implementation and the owners' log are unchanged by it, since it is declared after
the deliverable its type names.

The decision, given what a build shows of the project (`claim`, `sorter` and `implemented`, as
`LeanIntent.Execution.Read` would read them), finds nothing when `sorter`'s `main` reaches the
program (`runs`), and lists the deliverable, the executable and the program as reached
(`runs_listed`). Each change below is refused by name:

* an entry point that does not reach the program, as when `main` calls another function, or uses
  only the proof that the program fulfils the record (`unreached_refused`);
* an executable whose root module and what it imports declare no `main` (`noEntryPoint_refused`);
* a claim naming an executable that the project does not declare (`unknownExecutable_refused`);
* a claim whose type names a deliverable the project does not declare (`untied_refused`);
* a claim of a deliverable that no implementation is recorded for and that is not declared awaiting
  one (`unimplemented_refused`), and a project with no deliverable (`noDeliverable_refused`).

A claim of a deliverable declared awaiting its implementation is listed as awaiting, never as
reached (`awaiting_listed`, and `Execution.mem_reached` for every project). A deliverable no claim
names is listed as run by no executable, as a library function is, and an executable no claim names
as running no deliverable (`library_listed`); so is every deliverable of a project that declares no
executable (`noExecutable_listed`).
-/

namespace LeanIntentExamples.Execution

open LeanIntent LeanIntent.Execution LeanIntentExamples.Confirmation
  LeanIntentExamples.Implementation

/-! ## The claim -/

/-- The project's executable `sorter` runs the sorting deliverable. -/
def sorterRuns : Runs sortingDeliverable where
  executable := `sorter

/-! ## What the decision reads, accepts and refuses -/

/-- What the build shows of `sorterRuns`. -/
def claim : Claim := ⟨``sorterRuns, some ``sortingDeliverable, `sorter⟩

/-- The implementation recorded for the sorting deliverable, as the implementation check reports
it: the program, by its module and its name. -/
def implemented : List (Lean.Name × Implementation.Constant) := [(``sortingDeliverable, program)]

/-- What the build shows of the executable `sorter`: its root module `Sorter` declares `main`,
which reaches the program. -/
def sorter : Executable := ⟨`sorter, `Sorter, true, [program]⟩

theorem runs : findings [``sortingDeliverable] implemented [] [sorter] [claim] = [] := by
  decide +kernel

theorem runs_listed :
    (report [``sortingDeliverable] implemented [] [sorter] [claim]).reached =
      [(``sortingDeliverable, `sorter, program)] := by
  decide +kernel

theorem unreached_refused :
    findings [``sortingDeliverable] implemented [] [{ sorter with reaches := [] }] [claim] =
      [.unreached ``sortingDeliverable `sorter program] := by
  decide +kernel

theorem noEntryPoint_refused :
    findings [``sortingDeliverable] implemented []
      [{ sorter with entry := false, reaches := [] }] [claim] =
      [.noEntryPoint `sorter `Sorter] := by
  decide +kernel

theorem unknownExecutable_refused :
    findings [``sortingDeliverable] implemented [] [sorter] [{ claim with executable := `ghost }] =
      [.unknownExecutable ``sorterRuns `ghost] := by
  decide +kernel

theorem untied_refused :
    findings [``sortingDeliverable] implemented [] [sorter]
      [{ claim with deliverable := some `otherDeliverable }] =
      [.untied ``sorterRuns] := by
  decide +kernel

theorem unimplemented_refused :
    findings [``sortingDeliverable] [] [] [sorter] [claim] =
      [.unimplemented ``sortingDeliverable `sorter] := by
  decide +kernel

theorem noDeliverable_refused :
    findings [] implemented [] [sorter] [claim] = [.noDeliverable, .untied ``sorterRuns] := by
  decide +kernel

/-- Before the program exists, the deliverable is declared awaiting its implementation
(`LeanIntentExamples.Awaiting.sortingAwaiting`): the claim passes and is listed as awaiting, and
nothing is listed as reached. -/
theorem awaiting_listed :
    findings [``sortingDeliverable] [] [``sortingDeliverable] [{ sorter with reaches := [] }]
        [claim] = [] ∧
      (report [``sortingDeliverable] [] [``sortingDeliverable] [{ sorter with reaches := [] }]
        [claim]).awaiting = [(``sortingDeliverable, `sorter)] ∧
      (report [``sortingDeliverable] [] [``sortingDeliverable] [{ sorter with reaches := [] }]
        [claim]).reached = [] := by
  decide +kernel

/-- With no claim, the deliverable is listed as run by no executable, as a library function is,
and `sorter` as running no deliverable. -/
theorem library_listed :
    findings [``sortingDeliverable] implemented [] [sorter] [] = [] ∧
      (report [``sortingDeliverable] implemented [] [sorter] []).notRun = [``sortingDeliverable] ∧
      (report [``sortingDeliverable] implemented [] [sorter] []).idle = [`sorter] := by
  decide +kernel

/-- A project that declares no executable has every deliverable listed as run by none. -/
theorem noExecutable_listed :
    (report [``sortingDeliverable] implemented [] [] []).notRun = [``sortingDeliverable] := by
  decide +kernel

end LeanIntentExamples.Execution
