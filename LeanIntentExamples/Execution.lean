module

public import LeanIntent.Execution
public import LeanIntent.Execution.Code
public import LeanIntentExamples.Implementation
import all Init.Prelude

public section

namespace LeanIntentExamples.Execution

open LeanIntent LeanIntent.Execution LeanIntentExamples.Confirmation
  LeanIntentExamples.Implementation

@[expose] def sorterRuns : Runs sortingDeliverable where
  executable := `sorter

@[expose] def claim : Claim := ⟨``sorterRuns, some ``sortingDeliverable, `sorter⟩

@[expose] def implemented : List (Lean.Name × Implementation.Constant) := [(``sortingDeliverable, program)]

@[expose] def sorter : Executable := ⟨`sorter, `Sorter, true, [program]⟩

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

theorem awaiting_listed :
    findings [``sortingDeliverable] [] [``sortingDeliverable] [{ sorter with reaches := [] }]
        [claim] = [] ∧
      (report [``sortingDeliverable] [] [``sortingDeliverable] [{ sorter with reaches := [] }]
        [claim]).awaiting = [(``sortingDeliverable, `sorter)] ∧
      (report [``sortingDeliverable] [] [``sortingDeliverable] [{ sorter with reaches := [] }]
        [claim]).reached = [] := by
  decide +kernel

theorem library_listed :
    findings [``sortingDeliverable] implemented [] [sorter] [] = [] ∧
      (report [``sortingDeliverable] implemented [] [sorter] []).notRun = [``sortingDeliverable] ∧
      (report [``sortingDeliverable] implemented [] [sorter] []).idle = [`sorter] := by
  decide +kernel

theorem noExecutable_listed :
    (report [``sortingDeliverable] implemented [] [] []).notRun = [``sortingDeliverable] := by
  decide +kernel

theorem redArg_counted : isCompiledCodeOf [`c, `main].contains `c `c._redArg = true := by
  decide +kernel

theorem redArgOfRedArg_counted :
    isCompiledCodeOf [`c, `main].contains `c `c._redArg._redArg = true := by
  decide +kernel

theorem sharedClosedTerm_not_counted :
    isCompiledCodeOf [`c, `main].contains `c `c._closed_0 = false := by
  decide +kernel

theorem closedTermOfRedArg_not_counted :
    isCompiledCodeOf [`c, `main].contains `c `c._redArg._closed_0 = false := by
  decide +kernel

theorem constantNamedRedArg_not_counted :
    isCompiledCodeOf [`c, `c._redArg].contains `c `c._redArg = false := by
  decide +kernel

theorem specializationInside_not_counted :
    isCompiledCodeOf [`f, `c].contains `c `f._at_.c.spec_0 = false := by
  decide +kernel

theorem specialization_not_counted :
    isCompiledCodeOf [`c, `main].contains `c `c._at_.main.spec_0 = false := by
  decide +kernel

theorem specializationRedArg_not_counted :
    isCompiledCodeOf [`c, `main].contains `c `c._at_.main.spec_0._redArg = false := by
  decide +kernel

theorem lambda_not_counted : isCompiledCodeOf [`c, `main].contains `c `c._lam_0 = false := by
  decide +kernel

end LeanIntentExamples.Execution
